use ark_ff::{BigInteger, PrimeField};

pub fn eval_ule<F: PrimeField + From<i32>>(points: &[F], r: F) -> F {
    // Check if r is in interpolated set
    if F::ZERO <= r && r < F::from(points.len() as u64) {
        return points[usize::from_le_bytes(
            r.into_bigint().to_bytes_le()[0..8]
                .try_into()
                .expect("point too large"),
        )];
    }
    let (mut total, mut multiplier, mut inversions) = (F::ZERO, F::ONE, F::ONE);
    let length = points.len() as i32;

    for k in 1..points.len() {
        multiplier *= r - F::from(k as u64);
        inversions *= F::from(0 - (k as i32))
    }

    multiplier *= inversions.inverse().unwrap();
    total += multiplier * points[0];

    for i in 1..length {
        multiplier *= (r - F::from(i - 1))
            * ((r - F::from(i)) * F::from(i)).inverse().unwrap()
            * F::from(0 - (length - i));

        total += multiplier * points[i as usize]
    }
    return total;
}

#[test]
fn test_ule() {
    use ark_curve25519::Fr;

    let points = vec![Fr::from(0), Fr::from(1), Fr::from(4)];
    assert_eq!(eval_ule(&points, Fr::from(1)), Fr::from(1));
    assert_eq!(eval_ule(&points, Fr::from(3)), Fr::from(9))
}
