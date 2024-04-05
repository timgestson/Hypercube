use ark_ff::{BigInteger, PrimeField};
use itertools::Itertools;
use merlin::Transcript;

use crate::{
    fiatshamir::ProtocolTranscript,
    multilinear::{chis, eval_chis, eval_mle, set_variable, set_variable_second_half},
    sumcheck::{self, SumcheckProof},
    univariate::eval_ule,
};

pub fn prove<F: PrimeField + From<i32>>(
    a: &[F],
    b: &[F],
    c: &[F],
    transcript: &mut impl ProtocolTranscript<F>,
) -> SumcheckProof<F> {
    let r_len = (c.len().ilog2() / 2) as usize;
    transcript.append_points(b"mat_mult_a", &a);
    transcript.append_points(b"mat_mult_b", &b);
    transcript.append_points(b"mat_mult_c", &c);
    let r1 = transcript.challenge_scalars(b"mat_mult_r1", r_len);
    let r2 = transcript.challenge_scalars(b"mat_mult_r2", r_len);
    let fa = r1.iter().fold(a.to_vec(), |a, &r| set_variable(&a, r));
    let fb: Vec<F> = r2
        .iter()
        .fold(b.to_vec(), |b, &r| set_variable_second_half(&b, r));
    let r: Vec<F> = r1.into_iter().chain(r2.into_iter()).collect();
    let claim = eval_mle(&r, &c);
    let proof = SumcheckProof::prove(claim, vec![fa, fb], transcript);
    proof
}

pub fn verify<F: PrimeField + From<i32>>(
    a: &[F],
    b: &[F],
    c: &[F],
    sumcheck_proof: SumcheckProof<F>,
    transcript: &mut impl ProtocolTranscript<F>,
) {
    let r_len = (c.len().ilog2() / 2) as usize;
    transcript.append_points(b"mat_mult_a", &a);
    transcript.append_points(b"mat_mult_b", &b);
    transcript.append_points(b"mat_mult_c", &c);
    let r1 = transcript.challenge_scalars(b"mat_mult_r1", r_len);
    let r2 = transcript.challenge_scalars(b"mat_mult_r2", r_len);
    let (r3, expected_eval) = SumcheckProof::verify(&sumcheck_proof, transcript);

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
    let proof = prove(&a, &b, &c, &mut transcript);
    let mut vtranscript = Transcript::new(b"test_transcript");
    let rs = verify(&a, &b, &c, proof, &mut vtranscript);
}
