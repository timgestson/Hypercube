use std::f32::consts::E;
use std::iter::Product;
use std::mem;

use ark_ff::BigInteger;
use ark_ff::PrimeField;
use merlin::Transcript;

use crate::fiatshamir::ProtocolTranscript;
use crate::grandproduct;
use crate::grandproduct::GrandProductProof;
use crate::multilinear::chis;
use crate::multilinear::eval_chis;
use crate::multilinear::eval_mle;
use crate::multilinear::pad_next_power_of_two;
use crate::sumcheck;
use crate::sumcheck::SumcheckProof;
use crate::univariate::eval_ule;

fn densify<F: PrimeField>(
    matrix: &[F],
    row_count: usize,
    col_count: usize,
) -> (Vec<F>, Vec<usize>, Vec<usize>) {
    let (vals, rows, cols) = matrix.iter().enumerate().fold(
        (vec![], vec![], vec![]),
        |(mut vals, mut rows, mut cols), (i, &val)| {
            if !val.is_zero() {
                let row = i / col_count;
                let col = i % col_count;
                vals.push(val);
                rows.push(row);
                cols.push(col);
            }
            (vals, rows, cols)
        },
    );
    (vals, rows, cols)
}

fn to_bits<F: PrimeField>(f: F, size: usize) -> Vec<F> {
    let val = f.into_bigint().to_bits_le();
    let mut bits = vec![F::ZERO; size];
    for i in 0..size {
        if val[i] {
            bits[i] = F::ONE
        }
    }
    bits
}

struct SparkProof<F: PrimeField + From<i32>> {
    primary_sumcheck_proof: SumcheckProof<F>,
    row_grand_product_proof: GrandProductProof<F>,
    col_grand_product_proof: GrandProductProof<F>,
    vals: Vec<F>,
    e_rx: Vec<F>,
    e_ry: Vec<F>,
    read_rows: Vec<F>,
    read_cols: Vec<F>,
    counts_rows: Vec<F>,
    counts_cols: Vec<F>,
    memory: usize,
}

impl<F: PrimeField + From<i32>> SparkProof<F> {
    pub fn prove(
        vals: &[F],
        rows: &[usize],
        cols: &[usize],
        memory: usize,
        transcript: &mut impl ProtocolTranscript<F>,
    ) -> Self {
        let r = transcript.challenge_scalars(b"spark_challenge", memory.ilog2() as usize * 2);
        let (rx, ry) = r.split_at(memory.ilog2() as usize);

        let chi_rx = chis(rx);
        let chi_ry = chis(ry);

        let eq_rows: Vec<_> = (0..memory)
            .map(|i| eval_chis(&chi_rx, to_bits(F::from(i as u64), memory).as_ref()))
            .collect();

        let eq_cols: Vec<_> = (0..memory)
            .map(|i| eval_chis(&chi_ry, to_bits(F::from(i as u64), memory).as_ref()))
            .collect();

        let e_rx: Vec<_> = rows
            .iter()
            .map(|r| eval_chis(&chi_rx, to_bits(F::from(*r as u64), memory).as_slice()))
            .collect();
        let e_ry: Vec<_> = cols
            .iter()
            .map(|c| eval_chis(&chi_ry, to_bits(F::from(*c as u64), memory).as_slice()))
            .collect();

        let claim: F = (0..vals.len()).map(|i| vals[i] * e_rx[i] * e_ry[i]).sum();
        let primary_sumcheck_proof = SumcheckProof::prove(
            claim,
            vec![vals.to_vec(), e_rx.clone(), e_ry.clone()],
            transcript,
        );

        let row_reads: Vec<_> = rows.to_vec().iter().map(|&i| F::from(i as u64)).collect();
        let mut row_final = vec![F::ZERO; memory];
        for &r in rows.iter() {
            row_final[r] += F::ONE
        }
        let col_reads: Vec<_> = cols.to_vec().iter().map(|&i| F::from(i as u64)).collect();
        let mut col_final = vec![F::ZERO; memory];
        for &c in cols.iter() {
            col_final[c] += F::ONE
        }

        let gamma = transcript.challenge_scalar(b"spark_gamma");
        let tau = transcript.challenge_scalar(b"spark_tau");

        let fingerprint = |k: F, v: F, t: F| -> F { k * gamma.square() + v * gamma + t - tau };

        let mut r_products: Vec<_> = (0..memory)
            .map(|i| {
                let f = F::from(i as u64);
                (f, eval_chis(&chi_rx, &to_bits(f, memory)), F::ZERO)
            })
            .chain(
                (0..rows.len()).map(|i| (F::from(rows[i] as u64), e_rx[i], row_reads[i] + F::ONE)),
            )
            .map(|(a, b, c)| fingerprint(a, b, c))
            .collect();
        let r_claim = r_products.iter().fold(F::ONE, |a, &b| a * b);
        r_products = pad_next_power_of_two(&r_products);
        let row_proof = GrandProductProof::prove(&r_products, r_claim, transcript);

        let mut c_products: Vec<_> = (0..memory)
            .map(|i| {
                let f = F::from(i as u64);
                (f, eval_chis(&chi_ry, &to_bits(f, memory)), F::ZERO)
            })
            .chain(
                (0..rows.len()).map(|i| (F::from(rows[i] as u64), e_ry[i], col_reads[i] + F::ONE)),
            )
            .map(|(a, b, c)| fingerprint(a, b, c))
            .collect();
        let c_claim = c_products.iter().fold(F::ONE, |a, &b| a * b);
        c_products = pad_next_power_of_two(&c_products);
        let col_proof = GrandProductProof::prove(&c_products, c_claim, transcript);

        Self {
            row_grand_product_proof: row_proof,
            col_grand_product_proof: col_proof,
            primary_sumcheck_proof: primary_sumcheck_proof,
            vals: vals.to_vec(),
            e_rx: e_rx,
            e_ry: e_ry,
            read_rows: row_reads,
            read_cols: col_reads,
            counts_rows: row_final,
            counts_cols: col_final,
            memory: memory,
        }
    }

    pub fn verify(&self, transcript: &mut impl ProtocolTranscript<F>) {
        let r = transcript.challenge_scalars(b"spark_challenge", self.memory.ilog2() as usize * 2);
        let (rx, ry) = r.split_at(self.memory.ilog2() as usize);
        let (rz, eval) = self.primary_sumcheck_proof.verify(transcript);
        assert_eq!(
            self.primary_sumcheck_proof
                .final_terms
                .iter()
                .product::<F>(),
            eval
        );
        assert_eq!(
            eval_mle(&rz, &self.vals),
            self.primary_sumcheck_proof.final_terms[0]
        );
        assert_eq!(
            eval_mle(&rz, &self.e_rx),
            self.primary_sumcheck_proof.final_terms[1]
        );
        assert_eq!(
            eval_mle(&rz, &self.e_ry),
            self.primary_sumcheck_proof.final_terms[2]
        );

        let gamma = transcript.challenge_scalar(b"spark_gamma");
        let tau = transcript.challenge_scalar(b"spark_tau");
    }
}

#[test]
fn test_spark() {
    use ark_curve25519::Fr;
    let matrix = vec![
        Fr::from(0),
        Fr::from(2),
        Fr::from(7),
        Fr::from(0),
        Fr::from(0),
        Fr::from(0),
        Fr::from(10),
        Fr::from(0),
        Fr::from(0),
        Fr::from(2),
        Fr::from(0),
        Fr::from(0),
        Fr::from(0),
        Fr::from(0),
        Fr::from(0),
        Fr::from(0),
    ];
    let (vals, rows, cols) = densify(&matrix, 4, 4);

    println!("{:?}", vals);
    println!("{:?}", rows);
    println!("{:?}", cols);
    let mut transcript = Transcript::new(b"test_transcript");
    let proof = SparkProof::prove(&vals, &rows, &cols, matrix.len(), &mut transcript);
    let mut v_transcript = Transcript::new(b"test_transcript");
    proof.verify(&mut v_transcript);
}
