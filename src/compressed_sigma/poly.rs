#![allow(non_snake_case)]

use crate::compressed_sigma::amort::{amort_prove, amort_verify, AmortProof};
use crate::compressed_sigma::comp::{comp_prove, comp_verify, CompProof};
use crate::compressed_sigma::relations::{PolyMap, RPolyInstance, RPolyParams, RPolyWitness};
use ark_ec::CurveGroup;
use ark_ff::UniformRand;
use subroutines::poly_iop::prelude::PolyIOPErrors;
use transcript::IOPTranscript;

#[derive(Clone, Debug)]
pub struct PolyProof<G: CurveGroup> {
    pub mask_instance: RPolyInstance<G>,
    pub amort_proof: AmortProof<G>,
    pub comp_proof: CompProof<G>,
}

pub fn poly_prove<G: CurveGroup>(
    params: &RPolyParams<G>,
    instances: &[RPolyInstance<G>],
    witnesses: &[RPolyWitness<G>],
    optimized: bool,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<PolyProof<G>, PolyIOPErrors> {
    let m = params.g_vec.len();
    if instances.len() != witnesses.len() {
        return Err(PolyIOPErrors::InvalidParameters(
            "instances and witnesses length mismatch".to_string(),
        ));
    }

    let mut rng = ark_std::test_rng();
    let f0: Vec<G::ScalarField> = (0..m).map(|_| G::ScalarField::rand(&mut rng)).collect();
    let mut F0 = G::zero();
    for (g_i, f_i) in params.g_vec.iter().zip(f0.iter()) {
        F0 += g_i.mul(*f_i);
    }
    let v0: Vec<G::ScalarField> = f0.iter().map(|fi| params.h.eval(*fi)).collect();

    let mask_instance = RPolyInstance { F: F0, v: v0 };
    let mask_witness = RPolyWitness { f: f0 };

    let mut all_instances = Vec::with_capacity(instances.len() + 1);
    let mut all_witnesses = Vec::with_capacity(witnesses.len() + 1);
    all_instances.push(mask_instance.clone());
    all_witnesses.push(mask_witness);
    all_instances.extend_from_slice(instances);
    all_witnesses.extend_from_slice(witnesses);

    let (amort_instance, amort_witness, amort_proof) =
        amort_prove(params, &all_instances, &all_witnesses, optimized, transcript)
            .map_err(|e| PolyIOPErrors::InvalidParameters(format!("amort: {:?}", e)))?;

    let comp_proof =
        comp_prove(params, &amort_instance, &amort_witness, transcript)
            .map_err(|e| PolyIOPErrors::InvalidParameters(format!("comp: {:?}", e)))?;

    Ok(PolyProof {
        mask_instance,
        amort_proof,
        comp_proof,
    })
}

pub fn poly_verify<G: CurveGroup>(
    params: &RPolyParams<G>,
    instances: &[RPolyInstance<G>],
    proof: &PolyProof<G>,
    optimized: bool,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<(), PolyIOPErrors> {
    let mut all_instances = Vec::with_capacity(instances.len() + 1);
    all_instances.push(proof.mask_instance.clone());
    all_instances.extend_from_slice(instances);

    let amort_instance = amort_verify(params, &all_instances, &proof.amort_proof, optimized, transcript)
        .map_err(|e| PolyIOPErrors::InvalidParameters(format!("amort: {:?}", e)))?;

    comp_verify(params, &amort_instance, &proof.comp_proof, transcript)
        .map_err(|e| PolyIOPErrors::InvalidParameters(format!("comp: {:?}", e)))?;

    Ok(())
}
