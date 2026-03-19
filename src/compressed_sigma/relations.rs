#![allow(non_snake_case)]

use crate::errors::ArithErrors;
use crate::virtual_polynomial::{bit_decompose, eq_eval};
use ark_ec::CurveGroup;
use ark_ff::{PrimeField, Zero};

pub trait PolyMap<F: PrimeField> {
    fn degree(&self) -> usize;
    fn eval(&self, x: F) -> F;
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct DensePoly<F: PrimeField> {
    pub coeffs: Vec<F>,
}

impl<F: PrimeField> DensePoly<F> {
    pub fn new(coeffs: Vec<F>) -> Self {
        Self { coeffs }
    }
}

impl<F: PrimeField> PolyMap<F> for DensePoly<F> {
    fn degree(&self) -> usize {
        if self.coeffs.is_empty() {
            0
        } else {
            self.coeffs.len() - 1
        }
    }

    fn eval(&self, x: F) -> F {
        // Horner evaluation: c0 + c1 x + ... + cd x^d
        let mut acc = F::zero();
        for c in self.coeffs.iter().rev() {
            acc *= x;
            acc += c;
        }
        acc
    }
}

#[derive(Clone, Debug)]
pub struct RPolyParams<G: CurveGroup> {
    pub g_vec: Vec<G>,
    pub h: DensePoly<G::ScalarField>,
}

#[derive(Clone, Debug)]
pub struct RPolyInstance<G: CurveGroup> {
    pub F: G,
    pub v: Vec<G::ScalarField>,
}

#[derive(Clone, Debug)]
pub struct RPolyWitness<G: CurveGroup> {
    pub f: Vec<G::ScalarField>,
}

#[derive(Clone, Debug)]
pub struct RAmortPolyInstance<G: CurveGroup> {
    pub F: G,
    pub s: G::ScalarField,
    pub v_folded: Vec<G::ScalarField>,
    pub beta: Vec<G::ScalarField>,
}

#[derive(Clone, Debug)]
pub struct RAmortPolyWitness<G: CurveGroup> {
    pub f_folded: Vec<G::ScalarField>,
}

pub fn rpoly_check_commitment<G: CurveGroup>(
    params: &RPolyParams<G>,
    instance: &RPolyInstance<G>,
    witness: &RPolyWitness<G>,
) -> bool {
    if params.g_vec.len() != witness.f.len() {
        return false;
    }

    let mut acc = G::zero();
    for (g_i, f_i) in params.g_vec.iter().zip(witness.f.iter()) {
        acc += g_i.mul(*f_i);
    }
    acc == instance.F
}

pub fn rpoly_check_poly<G: CurveGroup>(
    params: &RPolyParams<G>,
    instance: &RPolyInstance<G>,
    witness: &RPolyWitness<G>,
) -> bool {
    if witness.f.len() != instance.v.len() {
        return false;
    }

    for (f_i, v_i) in witness.f.iter().zip(instance.v.iter()) {
        if params.h.eval(*f_i) != *v_i {
            return false;
        }
    }
    true
}

pub fn rpoly_check<G: CurveGroup>(
    params: &RPolyParams<G>,
    instance: &RPolyInstance<G>,
    witness: &RPolyWitness<G>,
) -> bool {
    rpoly_check_commitment(params, instance, witness)
        && rpoly_check_poly(params, instance, witness)
}

pub fn bits_as_field<F: PrimeField>(index_zero_based: usize, num_vars: usize) -> Vec<F> {
    let bits = bit_decompose(index_zero_based as u64, num_vars);
    bits.iter().map(|&b| F::from(b as u64)).collect()
}

pub fn eq_beta_bits<F: PrimeField>(beta: &[F], index_zero_based: usize) -> Result<F, ArithErrors> {
    let bits = bits_as_field::<F>(index_zero_based, beta.len());
    eq_eval(beta, &bits)
}

pub fn r_amort_poly_check<G: CurveGroup>(
    params: &RPolyParams<G>,
    instance: &RAmortPolyInstance<G>,
    witness: &RAmortPolyWitness<G>,
) -> bool {
    if params.g_vec.len() != witness.f_folded.len() {
        return false;
    }
    if witness.f_folded.len() != instance.v_folded.len() {
        return false;
    }

    // Commitment equation: sum_i f_i G_i = F
    let mut acc_g = G::zero();
    for (g_i, f_i) in params.g_vec.iter().zip(witness.f_folded.iter()) {
        acc_g += g_i.mul(*f_i);
    }
    if acc_g != instance.F {
        return false;
    }

    // Aggregated polynomial constraint:
    // sum_i eq(beta, Bits(i-1)) * (h(f_i) - v_i) = s
    let mut acc = G::ScalarField::zero();
    for (i, (f_i, v_i)) in witness
        .f_folded
        .iter()
        .zip(instance.v_folded.iter())
        .enumerate()
    {
        let w = match eq_beta_bits::<G::ScalarField>(&instance.beta, i) {
            Ok(w) => w,
            Err(_) => return false,
        };
        acc += w * (params.h.eval(*f_i) - *v_i);
    }

    acc == instance.s
}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_ec::Group;
    use ark_ff::UniformRand;
    use ark_std::ops::Mul;
    use ark_std::test_rng;
    use ark_test_curves::secp256k1::{Fr, G1Projective};

    #[test]
    fn dense_poly_eval_matches_naive() {
        let coeffs = vec![Fr::from(3u64), Fr::from(2u64), Fr::from(5u64)]; // 3 + 2x + 5x^2
        let h = DensePoly::new(coeffs);
        let x = Fr::from(7u64);
        let naive = Fr::from(3u64) + Fr::from(2u64) * x + Fr::from(5u64) * x * x;
        assert_eq!(h.eval(x), naive);
    }

    #[test]
    fn rpoly_check_accepts_valid() {
        let mut rng = test_rng();
        let m = 4;
        let g_vec: Vec<G1Projective> = (0..m)
            .map(|_| G1Projective::generator().mul(Fr::rand(&mut rng)))
            .collect();
        let f: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let h = DensePoly::new(vec![Fr::from(1u64), Fr::from(2u64)]); // 1 + 2x

        let mut F = G1Projective::zero();
        for (g_i, f_i) in g_vec.iter().zip(f.iter()) {
            F += g_i.mul(*f_i);
        }
        let v: Vec<Fr> = f.iter().map(|fi| h.eval(*fi)).collect();

        let params = RPolyParams { g_vec, h };
        let instance = RPolyInstance { F, v };
        let witness = RPolyWitness { f };

        assert!(rpoly_check(&params, &instance, &witness));
    }

    #[test]
    fn rpoly_check_rejects_invalid_v() {
        let mut rng = test_rng();
        let m = 4;
        let g_vec: Vec<G1Projective> = (0..m)
            .map(|_| G1Projective::generator().mul(Fr::rand(&mut rng)))
            .collect();
        let f: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let h = DensePoly::new(vec![Fr::from(1u64), Fr::from(2u64)]); // 1 + 2x

        let mut F = G1Projective::zero();
        for (g_i, f_i) in g_vec.iter().zip(f.iter()) {
            F += g_i.mul(*f_i);
        }
        let mut v: Vec<Fr> = f.iter().map(|fi| h.eval(*fi)).collect();
        v[0] += Fr::from(1u64);

        let params = RPolyParams { g_vec, h };
        let instance = RPolyInstance { F, v };
        let witness = RPolyWitness { f };

        assert!(!rpoly_check(&params, &instance, &witness));
    }

    #[test]
    fn r_amort_poly_check_accepts_valid() {
        let mut rng = test_rng();
        let m = 4;
        let logm = 2;
        let g_vec: Vec<G1Projective> = (0..m)
            .map(|_| G1Projective::generator().mul(Fr::rand(&mut rng)))
            .collect();
        let f_folded: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let h = DensePoly::new(vec![Fr::from(3u64), Fr::from(5u64)]); // 3 + 5x

        let mut F = G1Projective::zero();
        for (g_i, f_i) in g_vec.iter().zip(f_folded.iter()) {
            F += g_i.mul(*f_i);
        }
        let v_folded: Vec<Fr> = f_folded.iter().map(|fi| h.eval(*fi)).collect();
        let beta: Vec<Fr> = (0..logm).map(|_| Fr::rand(&mut rng)).collect();

        let mut s = Fr::zero();
        for (i, (f_i, v_i)) in f_folded.iter().zip(v_folded.iter()).enumerate() {
            let w = eq_beta_bits::<Fr>(&beta, i).unwrap();
            s += w * (h.eval(*f_i) - *v_i);
        }

        let params = RPolyParams { g_vec, h };
        let instance = RAmortPolyInstance {
            F,
            s,
            v_folded,
            beta,
        };
        let witness = RAmortPolyWitness { f_folded };

        assert!(r_amort_poly_check(&params, &instance, &witness));
    }

    #[test]
    fn r_amort_poly_check_rejects_invalid_s() {
        let mut rng = test_rng();
        let m = 4;
        let logm = 2;
        let g_vec: Vec<G1Projective> = (0..m)
            .map(|_| G1Projective::generator().mul(Fr::rand(&mut rng)))
            .collect();
        let f_folded: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let h = DensePoly::new(vec![Fr::from(3u64), Fr::from(5u64)]); // 3 + 5x

        let mut F = G1Projective::zero();
        for (g_i, f_i) in g_vec.iter().zip(f_folded.iter()) {
            F += g_i.mul(*f_i);
        }
        let v_folded: Vec<Fr> = f_folded.iter().map(|fi| h.eval(*fi)).collect();
        let beta: Vec<Fr> = (0..logm).map(|_| Fr::rand(&mut rng)).collect();

        let mut s = Fr::zero();
        for (i, (f_i, v_i)) in f_folded.iter().zip(v_folded.iter()).enumerate() {
            let w = eq_beta_bits::<Fr>(&beta, i).unwrap();
            s += w * (h.eval(*f_i) - *v_i);
        }
        s += Fr::from(1u64);

        let params = RPolyParams { g_vec, h };
        let instance = RAmortPolyInstance {
            F,
            s,
            v_folded,
            beta,
        };
        let witness = RAmortPolyWitness { f_folded };

        assert!(!r_amort_poly_check(&params, &instance, &witness));
    }
}
