use ark_ff::PrimeField;
use itertools::Itertools;
use merlin::Transcript;

use crate::{
    fiatshamir::ProtocolTranscript,
    sumcheck,
    multilinear::{chis, eval_eq, eval_mle},
    univariate::eval_ule,
};

fn compute_tree<F: PrimeField + From<i32>>(witness: &[F]) -> Vec<Vec<F>> {
    // TODO: Is this the best data structure? if so, optimize
    let num_layers = witness.len().ilog2() as usize;
    let mut last = witness.to_vec();
    let mut layers = vec![last.clone()];
    for _ in 0..(num_layers - 1) {
        let mut next = vec![];
        let half = last.len() / 2;
        for i in 0..half {
            next.push(last[i * 2] * last[i * 2 + 1])
        }
        layers.push(next.clone());
        last = next;
    }
    layers.reverse();
    layers
}

fn factor<F: PrimeField>(witness: &[F]) -> (Vec<F>, Vec<F>) {
    let half = witness.len() / 2;
    let (mut l, mut r) = (vec![], vec![]);
    for i in 0..half {
        l.push(witness[i * 2]);
        r.push(witness[i * 2 + 1]);
    }
    (l, r)
}

pub struct GrandProductProof<F: PrimeField + From<i32>> {
    claims: Vec<F>,
    left_evals: Vec<F>,
    right_evals: Vec<F>,
    sumcheck_proofs: Vec<Vec<Vec<F>>>
}

impl<F: PrimeField + From<i32>> GrandProductProof<F> {
    pub fn prove(
        witness: &[F],
        mut claim: F,
        transcript: &mut impl ProtocolTranscript<F>,
    ) -> Self {
        let layers = compute_tree(witness);
        transcript.append_scalar(b"grand_product_claim", &claim);
        let mut left_evals = vec![];
        let mut right_evals = vec![];
        let mut claims = vec![claim];
        let mut sumcheck_proofs = vec![];
        let mut z = vec![];
        let mut rands = vec![];

        let challenge = transcript.challenge_scalar(b"grand_product_challenge");
        rands.push(challenge);
        claim = eval_ule(&[layers[0][0], layers[0][1]], challenge);
        claims.push(claim);
        left_evals.push(layers[0][0]);
        right_evals.push(layers[0][1]);
        z.push(challenge);

        for i in 1..layers.len() {
            let layer = &layers[i];
            let eq: Vec<F> = chis(&z);
            let (l, r) = factor(layer);
            let (proof, rs, _) =
                sumcheck::prove(claim, vec![eq.clone(), l.clone(), r.clone()], transcript);
            sumcheck_proofs.push(proof);
            rands = rs;
            // TODO: Return from Sumcheck instead of recalculating
            let left = eval_mle(&rands, &l);
            let right = eval_mle(&rands, &r);
            left_evals.push(left);
            right_evals.push(right);
            transcript.append_scalar(b"grand_product_point", &left);
            transcript.append_scalar(b"grand_product_point", &right);
            let challenge = transcript.challenge_scalar(b"grand_product_challenge");
            rands.push(challenge);
            claim = eval_ule(&[left, right], challenge);
            claims.push(claim);
            z = rands;
        }
        Self {
            claims,
            left_evals,
            right_evals,
            sumcheck_proofs
        }
    }

    pub fn verify(
        &self,
        transcript: &mut impl ProtocolTranscript<F>,
    ) -> (F, Vec<F>) {
        transcript.append_scalar(b"grand_product_claim", &self.claims[0]);
        assert_eq!(self.left_evals.len(), self.right_evals.len());
        assert_eq!(self.left_evals.len(), self.claims.len() - 1);
        let mut z = vec![];
        assert_eq!(self.claims[0], self.left_evals[0] * self.right_evals[0]);
        let challenge = transcript.challenge_scalar(b"grand_product_challenge");
        z.push(challenge);

        for i in 1..self.claims.len() - 1 {
            let (rands, expected) =
                sumcheck::verify(self.claims[i], self.sumcheck_proofs[i - 1].clone(), 3, i, transcript);
            transcript.append_scalar(b"grand_product_point", &self.left_evals[i]);
            transcript.append_scalar(b"grand_product_point", &self.right_evals[i]);
            let challenge = transcript.challenge_scalar(b"grand_product_challenge");
            let eq = eval_eq(&z, &rands);
            assert_eq!(expected, eq * self.left_evals[i] * self.right_evals[i]);
            z = rands;
            z.push(challenge);
        }
        (*self.claims.last().unwrap(), z)
    }

}

pub fn prove<F: PrimeField + From<i32>>(
    witness: &[F],
    mut claim: F,
    transcript: &mut impl ProtocolTranscript<F>,
) -> (Vec<F>, Vec<F>, Vec<F>, Vec<Vec<Vec<F>>>) {
    let layers = compute_tree(witness);
    transcript.append_scalar(b"grand_product_claim", &claim);
    let mut left_evals = vec![];
    let mut right_evals = vec![];
    let mut claims = vec![claim];
    let mut sumcheck_proofs = vec![];
    let mut z = vec![];
    let mut rands = vec![];

    let challenge = transcript.challenge_scalar(b"grand_product_challenge");
    rands.push(challenge);
    claim = eval_ule(&[layers[0][0], layers[0][1]], challenge);
    claims.push(claim);
    left_evals.push(layers[0][0]);
    right_evals.push(layers[0][1]);
    z.push(challenge);

    for i in 1..layers.len() {
        let layer = &layers[i];
        let eq: Vec<F> = chis(&z);
        let (l, r) = factor(layer);
        let (proof, rs, _) =
            sumcheck::prove(claim, vec![eq.clone(), l.clone(), r.clone()], transcript);
        sumcheck_proofs.push(proof);
        rands = rs;
        // TODO: Return from Sumcheck instead of recalculating
        let left = eval_mle(&rands, &l);
        let right = eval_mle(&rands, &r);
        left_evals.push(left);
        right_evals.push(right);
        transcript.append_scalar(b"grand_product_point", &left);
        transcript.append_scalar(b"grand_product_point", &right);
        let challenge = transcript.challenge_scalar(b"grand_product_challenge");
        rands.push(challenge);
        claim = eval_ule(&[left, right], challenge);
        claims.push(claim);
        z = rands;
    }
    (claims, left_evals, right_evals, sumcheck_proofs)
}

pub fn verify<F: PrimeField + From<i32>>(
    claims: &[F],
    left_evals: &[F],
    right_evals: &[F],
    sumcheck_proofs: &[Vec<Vec<F>>],
    transcript: &mut impl ProtocolTranscript<F>,
) -> (F, Vec<F>) {
    transcript.append_scalar(b"grand_product_claim", &claims[0]);
    assert_eq!(left_evals.len(), right_evals.len());
    assert_eq!(left_evals.len(), claims.len() - 1);
    let mut z = vec![];
    assert_eq!(claims[0], left_evals[0] * right_evals[0]);
    let challenge = transcript.challenge_scalar(b"grand_product_challenge");
    z.push(challenge);

    for i in 1..claims.len() - 1 {
        let (rands, expected) =
            sumcheck::verify(claims[i], sumcheck_proofs[i - 1].clone(), 3, i, transcript);
        transcript.append_scalar(b"grand_product_point", &left_evals[i]);
        transcript.append_scalar(b"grand_product_point", &right_evals[i]);
        let challenge = transcript.challenge_scalar(b"grand_product_challenge");
        let eq = eval_eq(&z, &rands);
        assert_eq!(expected, eq * left_evals[i] * right_evals[i]);
        z = rands;
        z.push(challenge);
    }
    (*claims.last().unwrap(), z)
}

#[test]
fn grandproduct_test() {
    use ark_curve25519::Fr;
    let v2 = vec![
        Fr::from(2),
        Fr::from(1),
        Fr::from(2),
        Fr::from(2),
        Fr::from(2),
        Fr::from(1),
        Fr::from(7),
        Fr::from(1),
    ];
    let mut claim = Fr::from(2 * 4 * 2 * 7);

    let mut transcript = Transcript::new(b"test_transcript");
    let (claims, left, right, sc_proofs) = prove(&v2, claim, &mut transcript);
    let mut vtranscript = Transcript::new(b"test_transcript");
    let (final_claim, rands) = verify(&claims, &left, &right, &sc_proofs, &mut vtranscript);
    assert_eq!(final_claim, eval_mle(&rands, &v2));
}
