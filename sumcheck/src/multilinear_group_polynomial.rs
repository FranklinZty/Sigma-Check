// Copyright (c) 2023 Espresso Systems (espressosys.com)
// This file is part of the HyperPlonk library.

// You should have received a copy of the MIT License
// along with the HyperPlonk library. If not, see <https://mit-license.org/>.
use ark_poly::DenseMultilinearExtension;
use ark_ec::CurveGroup;
#[cfg(feature = "parallel")]
use rayon::prelude::{IndexedParallelIterator, IntoParallelRefMutIterator, ParallelIterator};

pub use my_poly::evaluations::multivariate::multilinear::DenseGroupMultilinearExtension;

pub fn fix_variables<G: CurveGroup>(
    poly: &DenseGroupMultilinearExtension<G>,
    partial_point: &[G::ScalarField],
) -> DenseGroupMultilinearExtension<G> {
    assert!(
        partial_point.len() <= poly.num_vars,
        "invalid size of partial point"
    );
    let nv = poly.num_vars;
    let mut poly = poly.evaluations.to_vec();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for (i, point) in partial_point.iter().enumerate().take(dim) {
        poly = fix_one_variable_helper(&poly, nv - i, point);
    }

    DenseGroupMultilinearExtension::<G>::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
}

fn fix_one_variable_helper<G: CurveGroup>(data: &[G], nv: usize, point: &G::ScalarField) -> Vec<G> {
    let mut res = vec![G::zero(); 1 << (nv - 1)];

    // evaluate single variable of partial point from left to right
    #[cfg(not(feature = "parallel"))]
    for i in 0..(1 << (nv - 1)) {
        res[i] = data[i] + (data[(i << 1) + 1] - data[i << 1]) * point;
    }

    #[cfg(feature = "parallel")]
    res.par_iter_mut().enumerate().for_each(|(i, x)| {
        *x = data[i << 1] + (data[(i << 1) + 1] - data[i << 1]).mul(point);
    });
    res
}

pub fn evaluate_no_par<G: CurveGroup>(poly: &DenseGroupMultilinearExtension<G>, point: &[G::ScalarField]) -> G {
    assert_eq!(poly.num_vars, point.len());
    fix_variables_no_par(poly, point).evaluations[0]
}

fn fix_variables_no_par<G: CurveGroup>(
    poly: &DenseGroupMultilinearExtension<G>,
    partial_point: &[G::ScalarField],
) -> DenseGroupMultilinearExtension<G> {
    assert!(
        partial_point.len() <= poly.num_vars,
        "invalid size of partial point"
    );
    let nv = poly.num_vars;
    let mut poly = poly.evaluations.to_vec();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for i in 1..dim + 1 {
        let r = partial_point[i - 1];
        for b in 0..(1 << (nv - i)) {
            poly[b] = poly[b << 1] + (poly[(b << 1) + 1] - poly[b << 1]).mul(r);
        }
    }
    DenseGroupMultilinearExtension::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
}

pub fn fix_last_variables<G: CurveGroup>(
    poly: &DenseGroupMultilinearExtension<G>,
    partial_point: &[G::ScalarField],
) -> DenseGroupMultilinearExtension<G> {
    assert!(
        partial_point.len() <= poly.num_vars,
        "invalid size of partial point"
    );
    let nv = poly.num_vars;
    let mut poly = poly.evaluations.to_vec();
    let dim = partial_point.len();
    // evaluate single variable of partial point from left to right
    for (i, point) in partial_point.iter().rev().enumerate().take(dim) {
        poly = fix_last_variable_helper(&poly, nv - i, point);
    }

    DenseGroupMultilinearExtension::<G>::from_evaluations_slice(nv - dim, &poly[..(1 << (nv - dim))])
}

fn fix_last_variable_helper<G: CurveGroup>(data: &[G], nv: usize, point: &G::ScalarField) -> Vec<G> {
    let half_len = 1 << (nv - 1);
    let mut res = vec![G::zero(); half_len];

    // evaluate single variable of partial point from left to right
    #[cfg(not(feature = "parallel"))]
    for b in 0..half_len {
        res[b] = data[b] + (data[b + half_len] - data[b]) * point;
    }

    #[cfg(feature = "parallel")]
    res.par_iter_mut().enumerate().for_each(|(i, x)| {
        *x = data[i] + (data[i + half_len] - data[i]).mul(point);
    });
    res
}

/// Given multilinear polynomial `p(x)` and s `s`, compute `s*p(x)`
pub fn scalar_mul_group_poly<G: CurveGroup>(
    poly: &DenseGroupMultilinearExtension<G>,
    s: &G::ScalarField,
) -> DenseGroupMultilinearExtension<G> {
    DenseGroupMultilinearExtension {
        evaluations: poly.evaluations.iter().map(|e| e.mul(s)).collect(),
        num_vars: poly.num_vars,
    }
}

/// Given multilinear polynomial `p(x)` and s `s`, compute `s*p(x)`
pub fn scalar_mul_group_scalar<G: CurveGroup>(
    poly: &DenseMultilinearExtension<G::ScalarField>,
    s: G,
) -> DenseGroupMultilinearExtension<G> {
    DenseGroupMultilinearExtension {
        evaluations: poly.evaluations.iter().map(|e| s.mul(e)).collect(),
        num_vars: poly.num_vars,
    }
}

/// Test-only methods used in virtual_polynomial.rs
#[cfg(test)]
pub mod testing_code {
    use super::*;
    use ark_ec::CurveGroup;
    use ark_bls12_381::G1Projective;
    use ark_std::rand::RngCore;
    use ark_std::{test_rng, UniformRand, end_timer, start_timer};
    use std::sync::Arc;

    /// Sample a random list of multilinear polynomials.
    /// Returns
    /// - the list of polynomials,
    /// - its sum of polynomial evaluations over the boolean hypercube.
    #[cfg(test)]
    pub fn random_group_mle_list<G: CurveGroup, R: RngCore>(
        nv: usize,
        g: G,
        degree: usize,
        rng: &mut R,
    ) -> (Vec<Arc<DenseGroupMultilinearExtension<G>>>, G) {
        let start = start_timer!(|| "sample random mle list");
        let mut multiplicands = Vec::with_capacity(degree);
        for _ in 0..degree {
            multiplicands.push(Vec::with_capacity(1 << nv))
        }
        let mut sum = G::zero();

        for _ in 0..(1 << nv) {
            let mut product = g;

            for e in multiplicands.iter_mut() {
                let val = G::ScalarField::rand(rng);
                e.push(g.mul(val));
                product = product.mul(val);
            }
            sum += product;
        }

        let list = multiplicands
            .into_iter()
            .map(|x| Arc::new(DenseGroupMultilinearExtension::from_evaluations_vec(nv, x)))
            .collect();

        end_timer!(start);
        (list, sum)
    }

    // Build a randomize list of mle-s whose sum is zero.
    #[cfg(test)]
    pub fn random_zero_mle_list<G: CurveGroup, R: RngCore>(
        nv: usize,
        g: G,
        degree: usize,
        rng: &mut R,
    ) -> (Vec<Arc<DenseGroupMultilinearExtension<G>>>, G) {
        let start = start_timer!(|| "sample random zero mle list");

        let mut multiplicands = Vec::with_capacity(degree);
        for _ in 0..degree {
            multiplicands.push(Vec::with_capacity(1 << nv))
        }
        let mut sum = G::zero();
        for _ in 0..(1 << nv) {
            multiplicands[0].push(G::zero());
            let mut product = G::zero();
            for e in multiplicands.iter_mut().skip(1) {
                let val = G::ScalarField::rand(rng);
                e.push(g.mul(val));
                product = product.mul(val);
            }
            sum += product;
        }

        let list = multiplicands
            .into_iter()
            .map(|x| Arc::new(DenseGroupMultilinearExtension::from_evaluations_vec(nv, x)))
            .collect();

        end_timer!(start);
        (list, sum)
    }

    #[test]
    fn test_multilinear_group_polynomial() {
        let mut rng = test_rng();
        let degree = 2;
        let nv = 2;
        let g = G1Projective::rand(&mut rng);
        let (list, sum) = random_group_mle_list(nv, g, degree, &mut rng);
        println!("sum = {}", sum);
        println!("list = {:#?}", list);
        let (list, sum) = random_zero_mle_list::<G1Projective, _>(nv, g, degree, &mut rng);
        println!("sum = {}", sum);
        println!("list = {:#?}", list);
    }
}