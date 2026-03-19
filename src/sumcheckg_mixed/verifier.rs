use super::structs::{IOPProverMessage, IOPVerifierState};
use crate::virtual_group_polynomial_mixed::VGPMAuxInfo;
use ark_ec::CurveGroup;
use ark_ff::Field;
use ark_std::{end_timer, start_timer, One};
use subroutines::poly_iop::prelude::PolyIOPErrors;
use transcript::IOPTranscript;

#[cfg(feature = "parallel")]
use rayon::iter::{IndexedParallelIterator, IntoParallelIterator, ParallelIterator};

pub fn verifier_init<G: CurveGroup>(aux: &VGPMAuxInfo<G>) -> IOPVerifierState<G> {
    let start = start_timer!(|| "sumcheck mixed verifier init");
    let res = IOPVerifierState {
        round: 1,
        num_vars: aux.num_variables,
        max_degree: aux.max_degree,
        finished: false,
        polynomials_received: Vec::with_capacity(aux.num_variables),
        challenges: Vec::with_capacity(aux.num_variables),
    };
    end_timer!(start);
    res
}

pub fn verify_round_and_update_state<G: CurveGroup>(
    state: &mut IOPVerifierState<G>,
    prover_msg: &IOPProverMessage<G>,
    transcript: &mut IOPTranscript<G::ScalarField>,
) -> Result<G::ScalarField, PolyIOPErrors> {
    let start = start_timer!(|| {
        format!("sumcheck mixed verify {}-th round", state.round)
    });

    if state.finished {
        return Err(PolyIOPErrors::InvalidVerifier(
            "Incorrect verifier state: finished".to_string(),
        ));
    }

    let challenge = transcript.get_and_append_challenge(b"Internal round")?;
    state.challenges.push(challenge);
    state.polynomials_received
        .push(prover_msg.evaluations.to_vec());

    if state.round == state.num_vars {
        state.finished = true;
    } else {
        state.round += 1;
    }

    end_timer!(start);
    Ok(challenge)
}

pub fn check_and_generate_subclaim<G: CurveGroup>(
    state: &IOPVerifierState<G>,
    asserted_sum: &G,
) -> Result<super::GroupSumCheckMixedSubClaim<G>, PolyIOPErrors> {
    let start = start_timer!(|| "sumcheck mixed final check");
    if !state.finished {
        return Err(PolyIOPErrors::InvalidVerifier(
            "Incorrect verifier state: not finished".to_string(),
        ));
    }
    if state.polynomials_received.len() != state.num_vars {
        return Err(PolyIOPErrors::InvalidVerifier(
            "insufficient rounds".to_string(),
        ));
    }

    #[cfg(feature = "parallel")]
    let mut expected_vec = state
        .polynomials_received
        .clone()
        .into_par_iter()
        .zip(state.challenges.clone().into_par_iter())
        .map(|(evaluations, challenge)| {
            if evaluations.len() != state.max_degree + 1 {
                return Err(PolyIOPErrors::InvalidVerifier(format!(
                    "incorrect number of evaluations: {} vs {}",
                    evaluations.len(),
                    state.max_degree + 1
                )));
            }
            interpolate_uni_group_poly::<G>(&evaluations, challenge)
        })
        .collect::<Result<Vec<_>, PolyIOPErrors>>()?;

    #[cfg(not(feature = "parallel"))]
    let mut expected_vec = state
        .polynomials_received
        .clone()
        .into_iter()
        .zip(state.challenges.clone().into_iter())
        .map(|(evaluations, challenge)| {
            if evaluations.len() != state.max_degree + 1 {
                return Err(PolyIOPErrors::InvalidVerifier(format!(
                    "incorrect number of evaluations: {} vs {}",
                    evaluations.len(),
                    state.max_degree + 1
                )));
            }
            interpolate_uni_group_poly::<G>(&evaluations, challenge)
        })
        .collect::<Result<Vec<_>, PolyIOPErrors>>()?;

    expected_vec.insert(0, *asserted_sum);

    for (evaluations, &expected) in state
        .polynomials_received
        .iter()
        .zip(expected_vec.iter())
        .take(state.num_vars)
    {
        if evaluations[0] + evaluations[1] != expected {
            return Err(PolyIOPErrors::InvalidProof(
                "Prover message is not consistent with the claim.".to_string(),
            ));
        }
    }

    end_timer!(start);
    Ok(super::GroupSumCheckMixedSubClaim {
        point: state.challenges.clone(),
        expected_evaluation: expected_vec[state.num_vars],
    })
}

pub fn interpolate_uni_group_poly<G: CurveGroup>(
    p_i: &[G],
    eval_at: G::ScalarField,
) -> Result<G, PolyIOPErrors> {
    let start = start_timer!(|| "sum check interpolate uni poly opt");
    let len = p_i.len();
    let mut res = G::zero();
    for i in 0..len {
        let mut num = G::ScalarField::one();
        let mut den = G::ScalarField::one();
        for j in 0..len {
            if i == j {
                continue;
            }
            num *= eval_at - G::ScalarField::from(j as u64);
            den *= G::ScalarField::from(i as u64) - G::ScalarField::from(j as u64);
        }
        res += p_i[i].mul(num * den.inverse().unwrap());
    }

    end_timer!(start);
    Ok(res)
}
