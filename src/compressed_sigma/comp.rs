#![allow(non_snake_case)]

use crate::compressed_sigma::encoding::{build_eq_mle, vec_to_mle_field, vec_to_mle_group};
use crate::compressed_sigma::relations::{PolyMap, RAmortPolyInstance, RAmortPolyWitness, RPolyParams};
use crate::errors::ArithErrors;
use crate::sumcheckg_mixed::GroupSumCheckMixed;
use crate::virtual_group_polynomial_mixed::VirtualGroupPolynomialMixed;
use ark_ec::CurveGroup;
use ark_ff::Zero;
use ark_poly::MultilinearExtension;
use std::sync::Arc;
use subroutines::poly_iop::prelude::PolyIOPErrors;
use transcript::{IOPTranscript, TranscriptError};

#[derive(Debug)]
pub enum CompError {
    Arith(ArithErrors),
    PolyIOP(PolyIOPErrors),
    Transcript(TranscriptError),
    InvalidParameters(String),
}

impl From<ArithErrors> for CompError {
    fn from(e: ArithErrors) -> Self {
        Self::Arith(e)
    }
}

impl From<PolyIOPErrors> for CompError {
    fn from(e: PolyIOPErrors) -> Self {
        Self::PolyIOP(e)
    }
}

impl From<TranscriptError> for CompError {
    fn from(e: TranscriptError) -> Self {
        Self::Transcript(e)
    }
}

#[derive(Clone, Debug)]
pub struct CompProof<G: CurveGroup> {
    pub sumcheck_proof: crate::sumcheckg_mixed::structs::IOPProof<G>,
    pub f_ry: G::ScalarField,
}

pub fn comp_prove<G: CurveGroup>(
    params: &RPolyParams<G>,
    instance: &RAmortPolyInstance<G>,
    witness: &RAmortPolyWitness<G>,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<CompProof<G>, CompError> {
    let m = params.g_vec.len();
    let logm = m.trailing_zeros() as usize;
    if (1usize << logm) != m {
        return Err(CompError::InvalidParameters(
            "g_vec length must be a power of two".to_string(),
        ));
    }
    if witness.f_folded.len() != m || instance.v_folded.len() != m {
        return Err(CompError::InvalidParameters(
            "folded vector length mismatch".to_string(),
        ));
    }

    let h_scalar = transcript.get_and_append_challenge(b"comp-H")?;
    let H = G::generator().mul(h_scalar);

    let f_mle = vec_to_mle_field(logm, &witness.f_folded);
    let v_mle = vec_to_mle_field(logm, &instance.v_folded);
    let G_mle = vec_to_mle_group(logm, &params.g_vec);
    let eq_beta = build_eq_mle(&instance.beta)?;

    let mut poly = VirtualGroupPolynomialMixed::new(logm);
    let f_idx = poly.add_scalar_mle(Arc::new(f_mle))?;
    let v_idx = poly.add_scalar_mle(Arc::new(v_mle))?;
    let eq_idx = poly.add_scalar_mle(eq_beta)?;
    let g_idx = poly.add_group_mle(Arc::new(G_mle))?;

    // p1 = f(y) * G(y)
    poly.add_product(Some(g_idx), vec![f_idx], G::zero())?;

    // p2 * H = eq(beta,y) * h(f(y)) * H - v(y) * H
    for (t, c) in params.h.coeffs.iter().enumerate() {
        if *c == G::ScalarField::zero() {
            continue;
        }
        if t == 0 {
            poly.add_product(None, vec![eq_idx], H.mul(*c))?;
        } else {
            let mut scalars = Vec::with_capacity(t + 1);
            scalars.push(eq_idx);
            for _ in 0..t {
                scalars.push(f_idx);
            }
            poly.add_product(None, scalars, H.mul(*c))?;
        }
    }
    poly.add_product(None, vec![eq_idx, v_idx], -H)?;

    let proof = <() as GroupSumCheckMixed<G>>::prove(&poly, transcript)?;

    let ry = proof.point.clone();
    let f_ry = poly.scalar_mles[f_idx].evaluate(&ry).unwrap();

    Ok(CompProof { sumcheck_proof: proof, f_ry })
}

pub fn comp_verify<G: CurveGroup>(
    params: &RPolyParams<G>,
    instance: &RAmortPolyInstance<G>,
    proof: &CompProof<G>,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<(), CompError> {
    let m = params.g_vec.len();
    let logm = m.trailing_zeros() as usize;
    if (1usize << logm) != m {
        return Err(CompError::InvalidParameters(
            "g_vec length must be a power of two".to_string(),
        ));
    }
    if instance.v_folded.len() != m {
        return Err(CompError::InvalidParameters(
            "v_folded length mismatch".to_string(),
        ));
    }

    let h_scalar = transcript.get_and_append_challenge(b"comp-H")?;
    let H = G::generator().mul(h_scalar);

    let v_mle = vec_to_mle_field(logm, &instance.v_folded);
    let G_mle = vec_to_mle_group(logm, &params.g_vec);

    let aux = crate::virtual_group_polynomial_mixed::VGPMAuxInfo::<G> {
        max_degree: std::cmp::max(params.h.degree() + 1, 2),
        num_variables: logm,
        phantom: std::marker::PhantomData,
    };

    let sum = instance.F + H.mul(instance.s);
    let subclaim = <() as GroupSumCheckMixed<G>>::verify(
        sum,
        &proof.sumcheck_proof,
        &aux,
        transcript,
    )?;

    let ry = &subclaim.point;
    let G_ry = G_mle.evaluate(ry);
    let v_val = v_mle.evaluate(ry).unwrap();
    let eq_val = crate::virtual_polynomial::eq_eval(&instance.beta, ry)?;

    let Pp = subclaim.expected_evaluation;
    let rhs = G_ry.mul(proof.f_ry)
        + H.mul(eq_val * (params.h.eval(proof.f_ry) - v_val));

    if Pp != rhs {
        return Err(CompError::InvalidParameters("leaf check failed".to_string()));
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compressed_sigma::relations::{eq_beta_bits, DensePoly, RAmortPolyInstance, RAmortPolyWitness, RPolyParams};
    use ark_ec::Group;
    use ark_ff::{UniformRand, Zero};
    use ark_std::ops::Mul;
    use ark_std::test_rng;
    use ark_test_curves::secp256k1::{Fr, G1Projective};
    use transcript::IOPTranscript;

    #[test]
    fn comp_roundtrip_small() {
        let mut rng = test_rng();
        let m = 4usize;
        let logm = 2usize;

        let g_vec: Vec<G1Projective> = (0..m)
            .map(|_| G1Projective::generator().mul(Fr::rand(&mut rng)))
            .collect();
        let h = DensePoly::new(vec![Fr::rand(&mut rng), Fr::rand(&mut rng), Fr::rand(&mut rng)]);

        let f_folded: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let v_folded: Vec<Fr> = (0..m).map(|_| Fr::rand(&mut rng)).collect();
        let beta: Vec<Fr> = (0..logm).map(|_| Fr::rand(&mut rng)).collect();

        let mut F = G1Projective::zero();
        for (g_i, f_i) in g_vec.iter().zip(f_folded.iter()) {
            F += g_i.mul(*f_i);
        }

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

        // sanity: check sum_y p(y) = F + s * H for the same H challenge
        let mut transcript_h = IOPTranscript::<Fr>::new(b"comp-test");
        transcript_h
            .append_serializable_element(b"domain-sep", &0u64)
            .unwrap();
        let h_scalar = transcript_h.get_and_append_challenge(b"comp-H").unwrap();
        let H = G1Projective::generator().mul(h_scalar);

        let mut p_sum = G1Projective::zero();
        for (i, (f_i, v_i)) in witness
            .f_folded
            .iter()
            .zip(instance.v_folded.iter())
            .enumerate()
        {
            let w = eq_beta_bits::<Fr>(&instance.beta, i).unwrap();
            let term = params.g_vec[i].mul(*f_i) + H.mul(w * (params.h.eval(*f_i) - *v_i));
            p_sum += term;
        }

        assert_eq!(p_sum, instance.F + H.mul(instance.s));

        let mut transcript = IOPTranscript::<Fr>::new(b"comp-test");
        transcript
            .append_serializable_element(b"domain-sep", &0u64)
            .unwrap();
        let proof = comp_prove(&params, &instance, &witness, &mut transcript).unwrap();

        let mut transcript_v = IOPTranscript::<Fr>::new(b"comp-test");
        transcript_v
            .append_serializable_element(b"domain-sep", &0u64)
            .unwrap();
        comp_verify(&params, &instance, &proof, &mut transcript_v).unwrap();
    }
}
