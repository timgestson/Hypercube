use ark_ff::PrimeField;

pub fn chis<F: PrimeField>(point: &[F]) -> Vec<F> {
    point.iter().fold(vec![F::ONE], |table, &r| {
        table
            .iter()
            .flat_map(|&t| vec![(F::ONE - r) * t, r * t])
            .collect()
    })
}

pub fn eval_eq<F: PrimeField>(a: &[F], b: &[F]) -> F {
    (0..a.len())
        .map(|i| a[i] * b[i] + (F::one() - a[i]) * (F::one() - b[i]))
        .product()
}

pub fn eval_chis<F: PrimeField>(chis: &[F], evals: &[F]) -> F {
    assert_eq!(chis.len(), evals.len());
    chis.iter().zip(evals).map(|(&a, &b)| a * b).sum()
}

pub fn eval_mle<F: PrimeField>(point: &[F], evals: &[F]) -> F {
    eval_chis(&chis(point), evals)
}

pub fn pad_next_power_of_two<F: PrimeField>(terms: &[F]) -> Vec<F> {
    let next = terms.len().next_power_of_two();
    let pad = vec![F::ZERO; next - terms.len()];
    terms.iter().cloned().chain(pad).collect()
}
