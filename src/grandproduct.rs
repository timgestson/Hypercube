use ark_ff::PrimeField;
use itertools::Itertools;
use merlin::Transcript;

use crate::{
    fiatshamir::ProtocolTranscript,
    linearsumcheck,
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

fn prove<F: PrimeField + From<i32>>(
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
    for i in 0..layers.len() {
        let layer = &layers[i];
        let eq: Vec<F> = chis(&z);
        let (l, r) = factor(layer);
        let (proof, rs) =
            linearsumcheck::prove(claim, vec![eq.clone(), l.clone(), r.clone()], transcript);
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

fn verify<F: PrimeField + From<i32>>(
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
    for i in 0..claims.len() - 1 {
        let (rands, expected) =
            linearsumcheck::verify(claims[i], sumcheck_proofs[i].clone(), 3, i, transcript);
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

/*
// hypercube eval
let y: F = (0..l.len().ilog2() as usize)
    .map(|_| vec![F::from(0), F::from(1)])
    .multi_cartesian_product()
    .map(|a| {
        eval_mle(&a, &eq) * eval_mle(&a, &r) * eval_mle(&a, &l)
    }).sum();
println!("hypercube eval: {}", y);
// end hypercube eval
*/
