use ark_ff::{BigInteger, PrimeField};
use merlin::Transcript;

use crate::{
    fiatshamir::ProtocolTranscript,
    multilinear::{chis, eval_chis},
    univariate::eval_ule,
};

fn set_variable<F: PrimeField>(mle: &[F], r: F) -> Vec<F> {
    let half = mle.len() / 2;
    let (a, b) = mle.split_at(half);
    a.iter()
        .zip(b)
        .map(|(&a, &b)| (F::ONE - r) * a + r * b)
        .collect()
}

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

pub fn prove<F: PrimeField + From<i32>>(
    claim: F,
    mut mles: Vec<Vec<F>>,
    transcript: &mut impl ProtocolTranscript<F>,
) -> (Vec<Vec<F>>, Vec<F>) {
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
    (polys, rs)
}

pub fn verify<F: PrimeField + From<i32>>(
    claim: F,
    polynomials: Vec<Vec<F>>,
    degree: usize,
    rounds: usize,
    transcript: &mut impl ProtocolTranscript<F>,
) -> (Vec<F>, F) {
    let mut rs = vec![F::ZERO; rounds];
    transcript.append_scalar(b"sumcheck_claim", &claim);
    transcript.append_scalar(b"sumcheck_degree", &F::from(degree as u64));
    transcript.append_scalar(b"sumcheck_rounds", &F::from(rounds as u64));
    transcript.append_points(b"sumcheck_points", &polynomials[0]);
    assert_eq!(claim, polynomials[0][0] + polynomials[0][1]);
    for i in 1..polynomials.len() {
        let r = transcript.challenge_scalar(b"sumcheck_challenge");
        assert_eq!(polynomials[i].len(), degree + 1);
        assert_eq!(
            eval_ule(&polynomials[i - 1], r),
            polynomials[i][0] + polynomials[i][1]
        );
        rs[i - 1] = r;
        transcript.append_points(b"sumcheck_points", &polynomials[i]);
    }
    if rounds == 0 {
        (rs, claim)
    } else {
        let r = transcript.challenge_scalar(b"sumcheck_challenge");
        let final_eval = eval_ule(&polynomials[rounds - 1], r);
        rs[rounds - 1] = r;
        (rs, final_eval)
    }
}

#[test]
fn quadratic() {
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

    let claim: Fr = a.iter().zip(&b).map(|(&a, &b)| a * b).sum();
    let mles = vec![a.clone(), b.clone()];

    let mut transcript = Transcript::new(b"test_transcript");

    let (polys, rs) = prove(claim, mles, &mut transcript);

    let mut verify_transcript = Transcript::new(b"test_transcript");
    let (vrs, expected_eval) = verify(claim, polys.clone(), 2, polys.len(), &mut verify_transcript);

    let rchis = chis(&vrs);
    let final_eval: Fr = eval_chis(&rchis, &a) * eval_chis(&rchis, &b);
    assert_eq!(final_eval, expected_eval);
}

#[test]
fn cubic() {
    use ark_curve25519::Fr;
    use itertools::izip;

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
    let c = vec![
        Fr::from(2),
        Fr::from(61),
        Fr::from(4),
        Fr::from(64),
        Fr::from(34),
        Fr::from(5),
        Fr::from(34),
        Fr::from(5),
    ];

    let claim: Fr = izip!(&a, &b, &c).map(|(&a, &b, &c)| a * b * c).sum();
    let mles = vec![a.clone(), b.clone(), c.clone()];
    let mut transcript = Transcript::new(b"test_transcript");
    let (polys, _rs) = prove(claim, mles, &mut transcript);

    let mut verify_transcript = Transcript::new(b"test_transcript");
    let (vrs, expected_eval) = verify(claim, polys.clone(), 3, polys.len(), &mut verify_transcript);

    let rchis = chis(&vrs);
    let final_eval: Fr = eval_chis(&rchis, &a) * eval_chis(&rchis, &b) * eval_chis(&rchis, &c);
    assert_eq!(expected_eval, final_eval);
}
