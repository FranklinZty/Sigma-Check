#![allow(non_snake_case)]

use crate::compressed_sigma::encoding::{build_eq_mle, eval_all_y, table_to_mle_yx, vec_to_mle_group};
use crate::compressed_sigma::relations::{bits_as_field, DensePoly, PolyMap, RAmortPolyInstance, RAmortPolyWitness, RPolyInstance, RPolyParams, RPolyWitness};
use crate::errors::ArithErrors;
use crate::sumcheck::structs::{IOPProof as FieldProof, IOPProverMessage as FieldMsg, IOPProverState as FieldProverState, IOPVerifierState as FieldVerifierState};
use crate::sumcheck::{SumCheckProver, SumCheckSubClaim, SumCheckVerifier};
use crate::sumcheckg::structs::{IOPProof as GroupProof, IOPProverMessage as GroupMsg, IOPProverState as GroupProverState, IOPVerifierState as GroupVerifierState};
use crate::sumcheckg::{GroupSumCheckProver, GroupSumCheckSubClaim, GroupSumCheckVerifier};
use crate::virtual_group_polynomial::{VGPAuxInfo, VirtualGroupPolynomial};
use crate::virtual_polynomial::{VPAuxInfo, VirtualPolynomial};
use ark_ec::CurveGroup;
use ark_ff::{PrimeField, Zero, One};
use std::sync::Arc;
use subroutines::poly_iop::prelude::PolyIOPErrors;
use transcript::{IOPTranscript, TranscriptError};

#[derive(Debug)]
pub enum AmortError {
    Arith(ArithErrors),
    PolyIOP(PolyIOPErrors),
    Transcript(TranscriptError),
    InvalidParameters(String),
}

impl From<ArithErrors> for AmortError {
    fn from(e: ArithErrors) -> Self {
        Self::Arith(e)
    }
}

impl From<PolyIOPErrors> for AmortError {
    fn from(e: PolyIOPErrors) -> Self {
        Self::PolyIOP(e)
    }
}

impl From<TranscriptError> for AmortError {
    fn from(e: TranscriptError) -> Self {
        Self::Transcript(e)
    }
}

#[derive(Clone, Debug)]
pub struct AmortProof<G: CurveGroup> {
    pub g2_proof: FieldProof<G::ScalarField>,
    pub g1_proof: Option<GroupProof<G>>,
    pub s: G::ScalarField,
    pub F: Option<G>,
}

pub fn amort_prove<G: CurveGroup>(
    params: &RPolyParams<G>,
    instances: &[RPolyInstance<G>],
    witnesses: &[RPolyWitness<G>],
    optimized: bool,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<(RAmortPolyInstance<G>, RAmortPolyWitness<G>, AmortProof<G>), AmortError> {
    if instances.len() != witnesses.len() {
        return Err(AmortError::InvalidParameters(
            "instances and witnesses length mismatch".to_string(),
        ));
    }
    if params.g_vec.is_empty() {
        return Err(AmortError::InvalidParameters("empty g_vec".to_string()));
    }

    let m = params.g_vec.len();
    let logm = m.trailing_zeros() as usize;
    if (1usize << logm) != m {
        return Err(AmortError::InvalidParameters(
            "g_vec length must be a power of two".to_string(),
        ));
    }

    // pad k to power of two by adding dummy instances
    let (instances_padded, witnesses_padded) = pad_instances(params, instances, witnesses)?;
    let k = instances_padded.len();
    let logk = k.trailing_zeros() as usize;

    // sample alpha, beta
    let alpha = sample_alpha(transcript, logk)?;
    let beta = sample_beta(transcript, logm)?;

    // build f and v tables
    let f_table = build_f_table(&witnesses_padded, m)?;
    let v_table = build_v_table(&instances_padded, m)?;

    let f_mle = table_to_mle_yx(&f_table)?.mle;
    let v_mle = table_to_mle_yx(&v_table)?.mle;

    // build g2 and run sum-check (always)
    let g2_poly = build_g2_poly::<G>(&f_mle, &v_mle, &alpha, &beta, &params.h, logk, logm)?;

    let (g2_proof, g1_proof, rx) = if optimized {
        let g2_proof = prove_single_sumcheck(&g2_poly, transcript)?;
        (g2_proof.clone(), None, g2_proof.point.clone())
    } else {
        let g1_poly = build_g1_poly(params, &instances_padded, &f_mle, &alpha, logk, logm)?;
        let (g1_proof, g2_proof) = prove_dual_sumcheck(&g1_poly, &g2_poly, transcript)?;
        let rx = g2_proof.point.clone();
        (g2_proof, Some(g1_proof), rx)
    };

    // compute folded witness and instance values
    let f_folded = eval_all_y(&f_mle, logk, logm, &rx)?;
    let v_folded = eval_all_y(&v_mle, logk, logm, &rx)?;

    let s = compute_s::<G>(&f_folded, &v_folded, &beta, &params.h)?;
    let F_x = compute_F_x(&instances_padded, &rx, logk)?;
    let F = if optimized {
        F_x
    } else {
        let F_sum = compute_F_from_folded(params, &f_folded)?;
        F_sum
    };

    let instance = RAmortPolyInstance {
        F,
        s,
        v_folded,
        beta: beta.clone(),
    };
    let witness = RAmortPolyWitness { f_folded };

    let proof = AmortProof {
        g2_proof,
        g1_proof,
        s,
        F: if optimized { None } else { Some(instance.F) },
    };

    Ok((instance, witness, proof))
}

pub fn amort_verify<G: CurveGroup>(
    params: &RPolyParams<G>,
    instances: &[RPolyInstance<G>],
    proof: &AmortProof<G>,
    optimized: bool,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<RAmortPolyInstance<G>, AmortError> {
    if params.g_vec.is_empty() {
        return Err(AmortError::InvalidParameters("empty g_vec".to_string()));
    }
    let m = params.g_vec.len();
    let logm = m.trailing_zeros() as usize;
    if (1usize << logm) != m {
        return Err(AmortError::InvalidParameters(
            "g_vec length must be a power of two".to_string(),
        ));
    }

    let instances_padded = pad_instances_only(params, instances)?;
    let k = instances_padded.len();
    let logk = k.trailing_zeros() as usize;

    let alpha = sample_alpha(transcript, logk)?;
    let beta = sample_beta(transcript, logm)?;

    let v_table = build_v_table(&instances_padded, m)?;
    let v_mle = table_to_mle_yx(&v_table)?.mle;

    let (g2_subclaim, g1_subclaim, rx) = if optimized {
        let aux = g2_aux_info(logk, params.h.degree());
        let g2_subclaim = verify_single_sumcheck(&aux, &proof.g2_proof, transcript)?;
        (g2_subclaim.clone(), None, g2_subclaim.point.clone())
    } else {
        let g1_aux = g1_aux_info(logk);
        let g2_aux = g2_aux_info(logk, params.h.degree());
        let g1_proof = proof
            .g1_proof
            .as_ref()
            .ok_or_else(|| AmortError::InvalidParameters("missing g1_proof".to_string()))?;
        let (g1_sub, g2_sub) =
            verify_dual_sumcheck(&g1_aux, &g2_aux, g1_proof, &proof.g2_proof, transcript)?;
        (g2_sub.clone(), Some(g1_sub), g2_sub.point.clone())
    };

    let ex = eq_eval_point(&alpha, &rx)?;

    // check g2: sg == ex * s
    if g2_subclaim.expected_evaluation != ex * proof.s {
        return Err(AmortError::InvalidParameters("g2 check failed".to_string()));
    }

    let F_x = compute_F_x(&instances_padded, &rx, logk)?;
    let F = if optimized {
        F_x
    } else {
        let F_sent = proof
            .F
            .ok_or_else(|| AmortError::InvalidParameters("missing F".to_string()))?;
        // check g1: Fg == ex * (F_x - F)
        let g1_sub = g1_subclaim.ok_or_else(|| AmortError::InvalidParameters("missing g1 subclaim".to_string()))?;
        if g1_sub.expected_evaluation != (F_x - F_sent) * ex {
            return Err(AmortError::InvalidParameters("g1 check failed".to_string()));
        }
        F_sent
    };

    let v_folded = eval_all_y(&v_mle, logk, logm, &rx)?;

    Ok(RAmortPolyInstance {
        F,
        s: proof.s,
        v_folded,
        beta,
    })
}

fn pad_instances<G: CurveGroup>(
    params: &RPolyParams<G>,
    instances: &[RPolyInstance<G>],
    witnesses: &[RPolyWitness<G>],
) -> Result<(Vec<RPolyInstance<G>>, Vec<RPolyWitness<G>>), AmortError> {
    let m = params.g_vec.len();
    for inst in instances.iter() {
        if inst.v.len() != m {
            return Err(AmortError::InvalidParameters(
                "instance v length mismatch".to_string(),
            ));
        }
    }
    for wit in witnesses.iter() {
        if wit.f.len() != m {
            return Err(AmortError::InvalidParameters(
                "witness f length mismatch".to_string(),
            ));
        }
    }

    let k = instances.len();
    let k2 = k.next_power_of_two();
    let mut instances_out = instances.to_vec();
    let mut witnesses_out = witnesses.to_vec();
    if k2 == k {
        return Ok((instances_out, witnesses_out));
    }

    let zero = G::ScalarField::zero();
    let h0 = params.h.eval(zero);
    let v_dummy = vec![h0; m];
    let f_dummy = vec![zero; m];

    for _ in k..k2 {
        instances_out.push(RPolyInstance {
            F: G::zero(),
            v: v_dummy.clone(),
        });
        witnesses_out.push(RPolyWitness { f: f_dummy.clone() });
    }

    Ok((instances_out, witnesses_out))
}

fn pad_instances_only<G: CurveGroup>(
    params: &RPolyParams<G>,
    instances: &[RPolyInstance<G>],
) -> Result<Vec<RPolyInstance<G>>, AmortError> {
    let m = params.g_vec.len();
    for inst in instances.iter() {
        if inst.v.len() != m {
            return Err(AmortError::InvalidParameters(
                "instance v length mismatch".to_string(),
            ));
        }
    }

    let k = instances.len();
    let k2 = k.next_power_of_two();
    let mut instances_out = instances.to_vec();
    if k2 == k {
        return Ok(instances_out);
    }

    let zero = G::ScalarField::zero();
    let h0 = params.h.eval(zero);
    let v_dummy = vec![h0; m];

    for _ in k..k2 {
        instances_out.push(RPolyInstance {
            F: G::zero(),
            v: v_dummy.clone(),
        });
    }

    Ok(instances_out)
}

fn build_f_table<G: CurveGroup>(witnesses: &[RPolyWitness<G>], m: usize) -> Result<Vec<Vec<G::ScalarField>>, AmortError> {
    let mut table = Vec::with_capacity(witnesses.len());
    for w in witnesses.iter() {
        if w.f.len() != m {
            return Err(AmortError::InvalidParameters(
                "witness f length mismatch".to_string(),
            ));
        }
        table.push(w.f.clone());
    }
    Ok(table)
}

fn build_v_table<G: CurveGroup>(instances: &[RPolyInstance<G>], m: usize) -> Result<Vec<Vec<G::ScalarField>>, AmortError> {
    let mut table = Vec::with_capacity(instances.len());
    for inst in instances.iter() {
        if inst.v.len() != m {
            return Err(AmortError::InvalidParameters(
                "instance v length mismatch".to_string(),
            ));
        }
        table.push(inst.v.clone());
    }
    Ok(table)
}

fn sample_alpha<F: PrimeField>(
    transcript: &mut IOPTranscript<F>,
    n: usize,
) -> Result<Vec<F>, AmortError> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let idx = i as u64;
        transcript.append_serializable_element(b"amort-alpha-index", &idx)?;
        let c = transcript.get_and_append_challenge(b"amort-alpha")?;
        out.push(c);
    }
    Ok(out)
}

fn sample_beta<F: PrimeField>(
    transcript: &mut IOPTranscript<F>,
    n: usize,
) -> Result<Vec<F>, AmortError> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        let idx = i as u64;
        transcript.append_serializable_element(b"amort-beta-index", &idx)?;
        let c = transcript.get_and_append_challenge(b"amort-beta")?;
        out.push(c);
    }
    Ok(out)
}

fn build_g2_poly<G: CurveGroup>(
    f_mle: &crate::multilinear_polynomial::DenseMultilinearExtension<G::ScalarField>,
    v_mle: &crate::multilinear_polynomial::DenseMultilinearExtension<G::ScalarField>,
    alpha: &[G::ScalarField],
    beta: &[G::ScalarField],
    h: &DensePoly<G::ScalarField>,
    logk: usize,
    logm: usize,
) -> Result<VirtualPolynomial<G::ScalarField>, AmortError> {
    let eq_alpha = build_eq_mle(alpha)?;
    let mut poly = VirtualPolynomial::new(logk);

    for y_idx in 0..(1usize << logm) {
        let y_bits = bits_as_field::<G::ScalarField>(y_idx, logm);
        let w = crate::virtual_polynomial::eq_eval(beta, &y_bits)?;
        let f_y = Arc::new(crate::multilinear_polynomial::fix_variables(f_mle, &y_bits));
        let v_y = Arc::new(crate::multilinear_polynomial::fix_variables(v_mle, &y_bits));

        // h(f_y) terms
        for (t, c) in h.coeffs.iter().enumerate() {
            if *c == G::ScalarField::zero() {
                continue;
            }
            if t == 0 {
                poly.add_mle_list(vec![eq_alpha.clone()], w * *c)?;
            } else {
                let mut list = Vec::with_capacity(t + 1);
                list.push(eq_alpha.clone());
                for _ in 0..t {
                    list.push(f_y.clone());
                }
                poly.add_mle_list(list, w * *c)?;
            }
        }

        // - w * eq_alpha * v_y
        poly.add_mle_list(vec![eq_alpha.clone(), v_y], -w)?;
    }

    Ok(poly)
}

fn build_g1_poly<G: CurveGroup>(
    params: &RPolyParams<G>,
    instances: &[RPolyInstance<G>],
    f_mle: &crate::multilinear_polynomial::DenseMultilinearExtension<G::ScalarField>,
    alpha: &[G::ScalarField],
    logk: usize,
    logm: usize,
) -> Result<VirtualGroupPolynomial<G>, AmortError> {
    let eq_alpha = build_eq_mle(alpha)?;
    let mut poly = VirtualGroupPolynomial::new(logk);

    // F~(x)
    for (j, inst) in instances.iter().enumerate() {
        let bits = bits_as_field::<G::ScalarField>(j, logk);
        let eq_x = build_eq_mle(&bits)?;
        poly.add_mle_list(vec![eq_x], inst.F)?;
    }

    // - sum_y f_y(x) * G_y
    for y_idx in 0..(1usize << logm) {
        let y_bits = bits_as_field::<G::ScalarField>(y_idx, logm);
        let f_y = Arc::new(crate::multilinear_polynomial::fix_variables(f_mle, &y_bits));
        let g_y = params.g_vec[y_idx];
        poly.add_mle_list(vec![f_y], -g_y)?;
    }

    // multiply by eq(alpha, x)
    poly.mul_by_mle(eq_alpha, G::ScalarField::one())?;

    Ok(poly)
}

fn prove_single_sumcheck<F: PrimeField>(
    poly: &VirtualPolynomial<F>,
    transcript: &mut IOPTranscript<F>,
) -> Result<FieldProof<F>, AmortError> {
    let mut prover_state = FieldProverState::prover_init(poly)?;
    let mut challenge: Option<F> = None;
    let mut prover_msgs = Vec::with_capacity(poly.aux_info.num_variables);
    for _ in 0..poly.aux_info.num_variables {
        let prover_msg = FieldProverState::prove_round_and_update_state(&mut prover_state, &challenge)?;
        transcript.append_serializable_element(b"g2 prover msg", &prover_msg)?;
        prover_msgs.push(prover_msg);
        challenge = Some(transcript.get_and_append_challenge(b"amort round")?);
    }
    if let Some(p) = challenge {
        prover_state.challenges.push(p)
    }
    Ok(FieldProof {
        point: prover_state.challenges,
        proofs: prover_msgs,
    })
}

fn verify_single_sumcheck<F: PrimeField>(
    aux: &VPAuxInfo<F>,
    proof: &FieldProof<F>,
    transcript: &mut IOPTranscript<F>,
) -> Result<SumCheckSubClaim<F>, AmortError> {
    let mut verifier_state = FieldVerifierState::verifier_init(aux);
    for i in 0..aux.num_variables {
        let prover_msg = proof.proofs.get(i).ok_or_else(|| {
            AmortError::InvalidParameters("incomplete g2 proof".to_string())
        })?;
        transcript.append_serializable_element(b"g2 prover msg", prover_msg)?;
        let challenge = transcript.get_and_append_challenge(b"amort round")?;
        verifier_update_with_challenge_field(&mut verifier_state, prover_msg, challenge)?;
    }
    let subclaim = verifier_state.check_and_generate_subclaim(&F::zero())?;
    Ok(subclaim)
}

fn prove_dual_sumcheck<G: CurveGroup>(
    g1: &VirtualGroupPolynomial<G>,
    g2: &VirtualPolynomial<G::ScalarField>,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<(GroupProof<G>, FieldProof<G::ScalarField>), AmortError> {
    if g1.aux_info.num_variables != g2.aux_info.num_variables {
        return Err(AmortError::InvalidParameters(
            "g1 and g2 num_variables mismatch".to_string(),
        ));
    }

    let mut prover_state_g1 = GroupProverState::prover_init(g1)?;
    let mut prover_state_g2 = FieldProverState::prover_init(g2)?;
    let mut challenge: Option<G::ScalarField> = None;

    let mut msgs_g1 = Vec::with_capacity(g1.aux_info.num_variables);
    let mut msgs_g2 = Vec::with_capacity(g2.aux_info.num_variables);

    for _ in 0..g1.aux_info.num_variables {
        let msg_g1 = GroupProverState::prove_round_and_update_state(&mut prover_state_g1, &challenge)?;
        let msg_g2 = FieldProverState::prove_round_and_update_state(&mut prover_state_g2, &challenge)?;
        transcript.append_serializable_element(b"g1 prover msg", &msg_g1)?;
        transcript.append_serializable_element(b"g2 prover msg", &msg_g2)?;
        msgs_g1.push(msg_g1);
        msgs_g2.push(msg_g2);
        challenge = Some(transcript.get_and_append_challenge(b"amort round")?);
    }

    if let Some(p) = challenge {
        prover_state_g1.challenges.push(p);
        prover_state_g2.challenges.push(p);
    }

    let g1_proof = GroupProof {
        point: prover_state_g1.challenges.clone(),
        proofs: msgs_g1,
    };
    let g2_proof = FieldProof {
        point: prover_state_g2.challenges.clone(),
        proofs: msgs_g2,
    };

    Ok((g1_proof, g2_proof))
}

fn verify_dual_sumcheck<G: CurveGroup>(
    g1_aux: &VGPAuxInfo<G>,
    g2_aux: &VPAuxInfo<G::ScalarField>,
    g1_proof: &GroupProof<G>,
    g2_proof: &FieldProof<G::ScalarField>,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<(GroupSumCheckSubClaim<G>, SumCheckSubClaim<G::ScalarField>), AmortError> {
    let mut v1 = GroupVerifierState::verifier_init(g1_aux);
    let mut v2 = FieldVerifierState::verifier_init(g2_aux);

    for i in 0..g1_aux.num_variables {
        let msg_g1 = g1_proof
            .proofs
            .get(i)
            .ok_or_else(|| AmortError::InvalidParameters("incomplete g1 proof".to_string()))?;
        let msg_g2 = g2_proof
            .proofs
            .get(i)
            .ok_or_else(|| AmortError::InvalidParameters("incomplete g2 proof".to_string()))?;
        transcript.append_serializable_element(b"g1 prover msg", msg_g1)?;
        transcript.append_serializable_element(b"g2 prover msg", msg_g2)?;
        let challenge = transcript.get_and_append_challenge(b"amort round")?;
        verifier_update_with_challenge_group(&mut v1, msg_g1, challenge)?;
        verifier_update_with_challenge_field(&mut v2, msg_g2, challenge)?;
    }

    let sub1 = v1.check_and_generate_subclaim(&G::zero())?;
    let sub2 = v2.check_and_generate_subclaim(&G::ScalarField::zero())?;
    Ok((sub1, sub2))
}

fn verifier_update_with_challenge_field<F: PrimeField>(
    state: &mut FieldVerifierState<F>,
    prover_msg: &FieldMsg<F>,
    challenge: F,
) -> Result<(), PolyIOPErrors> {
    if state.finished {
        return Err(PolyIOPErrors::InvalidVerifier(
            "verifier is already finished".to_string(),
        ));
    }
    state.challenges.push(challenge);
    state.polynomials_received.push(prover_msg.evaluations.to_vec());
    if state.round == state.num_vars {
        state.finished = true;
    } else {
        state.round += 1;
    }
    Ok(())
}

fn verifier_update_with_challenge_group<G: CurveGroup>(
    state: &mut GroupVerifierState<G>,
    prover_msg: &GroupMsg<G>,
    challenge: G::ScalarField,
) -> Result<(), PolyIOPErrors> {
    if state.finished {
        return Err(PolyIOPErrors::InvalidVerifier(
            "verifier is already finished".to_string(),
        ));
    }
    state.challenges.push(challenge);
    state.polynomials_received.push(prover_msg.evaluations.to_vec());
    if state.round == state.num_vars {
        state.finished = true;
    } else {
        state.round += 1;
    }
    Ok(())
}

fn compute_s<G: CurveGroup>(
    f_folded: &[G::ScalarField],
    v_folded: &[G::ScalarField],
    beta: &[G::ScalarField],
    h: &DensePoly<G::ScalarField>,
) -> Result<G::ScalarField, AmortError> {
    let logm = beta.len();
    let mut s = G::ScalarField::zero();
    for (i, (f_i, v_i)) in f_folded.iter().zip(v_folded.iter()).enumerate() {
        let bits = bits_as_field::<G::ScalarField>(i, logm);
        let w = crate::virtual_polynomial::eq_eval(beta, &bits)?;
        s += w * (h.eval(*f_i) - *v_i);
    }
    Ok(s)
}

fn compute_F_from_folded<G: CurveGroup>(
    params: &RPolyParams<G>,
    f_folded: &[G::ScalarField],
) -> Result<G, AmortError> {
    let mut acc = G::zero();
    for (g_i, f_i) in params.g_vec.iter().zip(f_folded.iter()) {
        acc += g_i.mul(*f_i);
    }
    Ok(acc)
}

fn compute_F_x<G: CurveGroup>(
    instances: &[RPolyInstance<G>],
    rx: &[G::ScalarField],
    logk: usize,
) -> Result<G, AmortError> {
    let mut evals = Vec::with_capacity(1usize << logk);
    for inst in instances.iter() {
        evals.push(inst.F);
    }
    let F_mle = vec_to_mle_group(logk, &evals);
    Ok(F_mle.evaluate(rx))
}

fn eq_eval_point<F: PrimeField>(x: &[F], y: &[F]) -> Result<F, AmortError> {
    Ok(crate::virtual_polynomial::eq_eval(x, y)?)
}

fn g2_aux_info<F: PrimeField>(logk: usize, deg_h: usize) -> VPAuxInfo<F> {
    let max_degree = std::cmp::max(deg_h + 1, 2);
    VPAuxInfo {
        max_degree,
        num_variables: logk,
        phantom: std::marker::PhantomData,
    }
}

fn g1_aux_info<G: CurveGroup>(logk: usize) -> VGPAuxInfo<G> {
    VGPAuxInfo {
        max_degree: 2,
        num_variables: logk,
        phantom: std::marker::PhantomData,
    }
}
