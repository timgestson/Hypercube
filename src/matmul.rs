use ark_ff::{BigInteger, PrimeField};
use itertools::Itertools;
use merlin::Transcript;

use crate::{
    fiatshamir::ProtocolTranscript,
    linearsumcheck,
    multilinear::{chis, eval_chis, eval_mle},
    univariate::eval_ule,
};

fn set_variable_first_half<F: PrimeField>(mle: &[F], r: F) -> Vec<F> {
    let half = mle.len() / 2;
    let (a, b) = mle.split_at(half);
    a.iter()
        .zip(b)
        .map(|(&a, &b)| (F::ONE - r) * a + r * b)
        .collect()
}

fn set_variable_second_half<F: PrimeField>(mle: &[F], r: F) -> Vec<F> {
    mle.chunks(2)
        .map(|a| (F::ONE - r) * a[0] + r * a[1])
        .collect()
}

pub fn prove<F: PrimeField + From<i32>>(
    a: &[F],
    b: &[F],
    c: &[F],
    transcript: &mut impl ProtocolTranscript<F>,
) -> (F, Vec<Vec<F>>, Vec<F>) {
    let r_len = (c.len().ilog2() / 2) as usize;
    transcript.append_points(b"mat_mult_a", &a);
    transcript.append_points(b"mat_mult_b", &b);
    transcript.append_points(b"mat_mult_c", &c);
    let r1 = transcript.challenge_scalars(b"mat_mult_r1", r_len);
    let r2 = transcript.challenge_scalars(b"mat_mult_r2", r_len);
    let fa = r1
        .iter()
        .fold(a.to_vec(), |a, &r| set_variable_first_half(&a, r));
    let fb: Vec<F> = r2
        .iter()
        .fold(b.to_vec(), |b, &r| set_variable_second_half(&b, r));
    let r: Vec<F> = r1.into_iter().chain(r2.into_iter()).collect();
    let claim = eval_mle(&r, &c);

    let (polys, rs) = linearsumcheck::prove(claim, vec![fa, fb], transcript);
    (claim, polys, rs)
}

pub fn verify<F: PrimeField + From<i32>>(
    a: &[F],
    b: &[F],
    c: &[F],
    claim: F,
    sumcheck_polys: Vec<Vec<F>>,
    transcript: &mut impl ProtocolTranscript<F>,
) {
    let r_len = (c.len().ilog2() / 2) as usize;
    transcript.append_points(b"mat_mult_a", &a);
    transcript.append_points(b"mat_mult_b", &b);
    transcript.append_points(b"mat_mult_c", &c);
    let r1 = transcript.challenge_scalars(b"mat_mult_r1", r_len);
    let r2 = transcript.challenge_scalars(b"mat_mult_r2", r_len);
    let (r3, expected_eval) = linearsumcheck::verify(claim, sumcheck_polys, 2, r_len, transcript);

    let fa_r: Vec<F> = r1.into_iter().chain(r3.clone().into_iter()).collect();
    let fb_r: Vec<F> = r3.into_iter().chain(r2.into_iter()).collect();
    assert_eq!(expected_eval, eval_mle(&fa_r, &a) * eval_mle(&fb_r, &b));
}

#[test]
fn matrix() {
    use ark_curve25519::Fr;

    let a = vec![Fr::from(1), Fr::from(0), Fr::from(0), Fr::from(1)];
    let b = vec![Fr::from(4), Fr::from(1), Fr::from(2), Fr::from(2)];
    let c = vec![Fr::from(4), Fr::from(1), Fr::from(2), Fr::from(2)];
    let mut transcript = Transcript::new(b"test_transcript");
    let (claim, polys, _rs) = prove(&a, &b, &c, &mut transcript);
    let mut vtranscript = Transcript::new(b"test_transcript");
    verify(&a, &b, &c, claim, polys, &mut vtranscript);
}
