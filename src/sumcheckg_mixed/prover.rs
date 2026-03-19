use super::structs::{IOPProverMessage, IOPProverState};
use crate::multilinear_group_polynomial;
use crate::multilinear_polynomial;
use ark_ec::CurveGroup;
use ark_ff::{One, Zero};
use rayon::prelude::*;
use subroutines::poly_iop::prelude::PolyIOPErrors;

pub fn prover_init<G: CurveGroup>(
    poly: &crate::virtual_group_polynomial_mixed::VirtualGroupPolynomialMixed<G>,
) -> Result<IOPProverState<G>, PolyIOPErrors> {
    if poly.num_variables == 0 {
        return Err(PolyIOPErrors::InvalidParameters(
            "Attempt to prove a constant.".to_string(),
        ));
    }

    let aux = poly.aux_info();

    Ok(IOPProverState {
        challenges: Vec::with_capacity(poly.num_variables),
        round: 0,
        num_vars: poly.num_variables,
        max_degree: aux.max_degree,
        poly: poly.clone(),
    })
}

pub fn prove_round_and_update_state<G: CurveGroup>(
    state: &mut IOPProverState<G>,
    challenge: &Option<G::ScalarField>,
) -> Result<IOPProverMessage<G>, PolyIOPErrors> {
    if state.round >= state.num_vars {
        return Err(PolyIOPErrors::InvalidProver(
            "Prover is not active".to_string(),
        ));
    }

    // fix variables for all mles
    if let Some(chal) = challenge {
        if state.round == 0 {
            return Err(PolyIOPErrors::InvalidProver(
                "first round should be prover first.".to_string(),
            ));
        }
        state.challenges.push(*chal);
        let r = state.challenges[state.round - 1];

        state
            .poly
            .scalar_mles
            .par_iter_mut()
            .for_each(|mle| {
                *mle = std::sync::Arc::new(multilinear_polynomial::fix_variables(mle, &[r]));
            });
        state
            .poly
            .group_mles
            .par_iter_mut()
            .for_each(|mle| {
                *mle = std::sync::Arc::new(multilinear_group_polynomial::fix_variables(mle, &[r]));
            });
    } else if state.round > 0 {
        return Err(PolyIOPErrors::InvalidProver(
            "verifier message is empty".to_string(),
        ));
    }

    state.round += 1;

    let remaining = state.num_vars - state.round;
    let size = 1usize << remaining;

    let mut sums = vec![G::zero(); state.max_degree + 1];

    for (group_idx, scalars, coeff) in state.poly.products.iter() {
        let mut scalar_evals = vec![G::ScalarField::zero(); scalars.len()];
        let mut scalar_steps = vec![G::ScalarField::zero(); scalars.len()];

        for b in 0..size {
            for (i, &s_idx) in scalars.iter().enumerate() {
                let table = &state.poly.scalar_mles[s_idx];
                scalar_evals[i] = table[b << 1];
                scalar_steps[i] = table[(b << 1) + 1] - table[b << 1];
            }

            let (mut g_eval, g_step) = if let Some(gi) = group_idx {
                let g_table = &state.poly.group_mles[*gi];
                let g0 = g_table.evaluations[b << 1];
                let g1 = g_table.evaluations[(b << 1) + 1];
                (g0, g1 - g0)
            } else {
                (G::zero(), G::zero())
            };

            let mut scalars_t = scalar_evals.clone();

            for t in 0..=state.max_degree {
                let mut scalar_prod = G::ScalarField::one();
                for val in scalars_t.iter() {
                    scalar_prod *= *val;
                }

                let term = (*coeff + g_eval).mul(scalar_prod);
                sums[t] += term;

                for (val, step) in scalars_t.iter_mut().zip(scalar_steps.iter()) {
                    *val += *step;
                }
                g_eval += g_step;
            }
        }
    }

    Ok(IOPProverMessage { evaluations: sums })
}
