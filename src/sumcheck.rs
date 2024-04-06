use ark_ff::{BigInteger, PrimeField};
use merlin::Transcript;

use crate::{
    fiatshamir::ProtocolTranscript,
    multilinear::{chis, eval_chis, set_variable},
    univariate::eval_ule,
};

fn derive_points<F: PrimeField>(mles: &[Vec<F>], last_claim: F) -> Vec<F> {
    let degree = mles.len() + 1;
    let mle_len = mles[0].len();
    let mle_half = mle_len / 2;
    let mut points = vec![F::ZERO; degree];
    for i in 0..mle_half {
        for j in 0..degree {
            if j == 1 {
                points[j] = last_claim - points[0];
            } else {
                let t = F::from(j as u64);
                let mut product = F::ONE;
                for k in 0..mles.len() {
                    product *= mles[k][i] * (F::ONE - t) + mles[k][i + mle_half] * t;
                }
                points[j] += product
            }
        }
    }
    points
}

#[derive(Clone)]
pub struct SumcheckProof<F: PrimeField + From<i32>> {
    pub polynomials: Vec<Vec<F>>,
    pub rands: Vec<F>,
    pub final_terms: Vec<F>,
    pub degree: usize,
    pub rounds: usize,
    pub claim: F,
}

impl<F: PrimeField + From<i32>> SumcheckProof<F> {
    pub fn prove(
        claim: F,
        mut mles: Vec<Vec<F>>,
        transcript: &mut impl ProtocolTranscript<F>,
    ) -> Self {
        transcript.append_scalar(b"sumcheck_claim", &claim);
        let degree = mles.len();
        transcript.append_scalar(b"sumcheck_degree", &F::from(degree as u64));
        let mle_len = mles[0].len();
        let rounds = mle_len.ilog2() as usize;
        transcript.append_scalar(b"sumcheck_rounds", &F::from(rounds as u64));
        let mut rs = vec![F::ZERO; rounds];
        let mut last_claim = claim;
        let points = derive_points(&mles, last_claim);
        transcript.append_points(b"sumcheck_points", &points);
        let mut polys = vec![points];
        for i in 1..rounds {
            let r = transcript.challenge_scalar(b"sumcheck_challenge");
            for j in 0..mles.len() {
                mles[j] = set_variable(&mles[j], r);
            }
            last_claim = eval_ule(&polys[i - 1], r);
            let points = derive_points(&mles, last_claim);
            transcript.append_points(b"sumcheck_points", &points);
            polys.push(points);
            rs[i - 1] = r;
        }
        let r = transcript.challenge_scalar(b"sumcheck_challenge");
        rs[rounds - 1] = r;
        let finals = mles.iter().map(|mle| set_variable(mle, r)[0]).collect();
        SumcheckProof {
            polynomials: polys,
            final_terms: finals,
            rands: rs,
            degree: degree,
            rounds: rounds,
            claim: claim,
        }
    }

    pub fn verify(&self, transcript: &mut impl ProtocolTranscript<F>) -> (Vec<F>, F) {
        let mut rs = vec![F::ZERO; self.rounds];
        transcript.append_scalar(b"sumcheck_claim", &self.claim);
        transcript.append_scalar(b"sumcheck_degree", &F::from(self.degree as u64));
        transcript.append_scalar(b"sumcheck_rounds", &F::from(self.rounds as u64));
        transcript.append_points(b"sumcheck_points", &self.polynomials[0]);
        assert_eq!(self.claim, self.polynomials[0][0] + self.polynomials[0][1]);
        for i in 1..self.polynomials.len() {
            let r = transcript.challenge_scalar(b"sumcheck_challenge");
            assert_eq!(self.polynomials[i].len(), self.degree + 1);
            assert_eq!(
                eval_ule(&self.polynomials[i - 1], r),
                self.polynomials[i][0] + self.polynomials[i][1]
            );
            rs[i - 1] = r;
            transcript.append_points(b"sumcheck_points", &self.polynomials[i]);
        }
        if self.rounds == 0 {
            (rs, self.claim)
        } else {
            let r = transcript.challenge_scalar(b"sumcheck_challenge");
            let final_eval = eval_ule(&self.polynomials[self.rounds - 1], r);
            rs[self.rounds - 1] = r;
            (rs, final_eval)
        }
    }
}

#[test]
fn test() {
    use ark_curve25519::Fr;

    let a = vec![
        Fr::from(9),
        Fr::from(91),
        Fr::from(34),
        Fr::from(5),
        Fr::from(34),
        Fr::from(5),
        Fr::from(34),
        Fr::from(5),
    ];
    let b = vec![
        Fr::from(2),
        Fr::from(61),
        Fr::from(4),
        Fr::from(64),
        Fr::from(34),
        Fr::from(5),
        Fr::from(34),
        Fr::from(5),
    ];
    let mut transcript = Transcript::new(b"test_transcript");
    let mut verify_transcript = Transcript::new(b"test_transcript");

    let claim: Fr = a.iter().zip(&b).map(|(&a, &b)| a * b).sum();
    let mles = vec![a.clone(), b.clone()];

    let proof = SumcheckProof::prove(claim, mles, &mut transcript);
    let (vrs, expected_eval) = proof.verify(&mut verify_transcript);

    let rchis = chis(&vrs);
    let final_eval: Fr = eval_chis(&rchis, &a) * eval_chis(&rchis, &b);
    assert_eq!(final_eval, expected_eval);
}
