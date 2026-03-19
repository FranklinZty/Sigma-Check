use crate::virtual_group_polynomial_mixed::{VGPMAuxInfo, VirtualGroupPolynomialMixed};
use ark_ec::CurveGroup;
use ark_std::{end_timer, start_timer};
use std::fmt::Debug;

use subroutines::poly_iop::prelude::PolyIOPErrors;
use transcript::IOPTranscript;

mod prover;
pub mod structs;
mod verifier;

use prover::{prove_round_and_update_state, prover_init};
use structs::IOPProof;
use verifier::{check_and_generate_subclaim, verifier_init, verify_round_and_update_state};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GroupSumCheckMixedSubClaim<G: CurveGroup> {
    pub point: Vec<G::ScalarField>,
    pub expected_evaluation: G,
}

pub trait GroupSumCheckMixed<G: CurveGroup> {
    type VirtualGroupPolynomialMixed;
    type AuxInfo;
    type GroupSumCheckProof: Clone + Debug + Default + PartialEq;
    type Transcript;
    type GroupSumCheckSubClaim: Clone + Debug + Default + PartialEq;

    fn extract_sum(proof: &Self::GroupSumCheckProof) -> G;
    fn init_transcript() -> Self::Transcript;

    fn prove(
        poly: &Self::VirtualGroupPolynomialMixed,
        transcript: &mut Self::Transcript,
    ) -> Result<Self::GroupSumCheckProof, PolyIOPErrors>;

    fn verify(
        sum: G,
        proof: &Self::GroupSumCheckProof,
        aux_info: &Self::AuxInfo,
        transcript: &mut Self::Transcript,
    ) -> Result<Self::GroupSumCheckSubClaim, PolyIOPErrors>;
}

impl<G: CurveGroup> GroupSumCheckMixed<G> for () {
    type VirtualGroupPolynomialMixed = VirtualGroupPolynomialMixed<G>;
    type AuxInfo = VGPMAuxInfo<G>;
    type GroupSumCheckProof = IOPProof<G>;
    type Transcript = IOPTranscript<G::ScalarField>;
    type GroupSumCheckSubClaim = GroupSumCheckMixedSubClaim<G>;

    fn extract_sum(proof: &Self::GroupSumCheckProof) -> G {
        let start = start_timer!(|| "extract sum");
        let res = proof.proofs[0].evaluations[0] + proof.proofs[0].evaluations[1];
        end_timer!(start);
        res
    }

    fn init_transcript() -> Self::Transcript {
        let start = start_timer!(|| "init transcript");
        let res = IOPTranscript::<G::ScalarField>::new(b"Initializing SumCheckMixed transcript");
        end_timer!(start);
        res
    }

    fn prove(
        poly: &Self::VirtualGroupPolynomialMixed,
        transcript: &mut Self::Transcript,
    ) -> Result<Self::GroupSumCheckProof, PolyIOPErrors> {
        let start = start_timer!(|| "sum check mixed prove");

        let aux = poly.aux_info();
        transcript.append_serializable_element(b"aux info", &aux)?;

        let mut prover_state = prover_init(poly)?;
        let mut challenge = None;
        let mut prover_msgs = Vec::with_capacity(aux.num_variables);
        for _ in 0..aux.num_variables {
            let prover_msg = prove_round_and_update_state(&mut prover_state, &challenge)?;
            transcript.append_serializable_element(b"prover msg", &prover_msg)?;
            prover_msgs.push(prover_msg);
            challenge = Some(transcript.get_and_append_challenge(b"Internal round")?);
        }
        if let Some(p) = challenge {
            prover_state.challenges.push(p)
        };

        end_timer!(start);
        Ok(IOPProof {
            point: prover_state.challenges,
            proofs: prover_msgs,
        })
    }

    fn verify(
        sum: G,
        proof: &Self::GroupSumCheckProof,
        aux_info: &Self::AuxInfo,
        transcript: &mut Self::Transcript,
    ) -> Result<Self::GroupSumCheckSubClaim, PolyIOPErrors> {
        let start = start_timer!(|| "sum check mixed verify");

        transcript.append_serializable_element(b"aux info", aux_info)?;
        let mut verifier_state = verifier_init(aux_info);
        for i in 0..aux_info.num_variables {
            let prover_msg = proof.proofs.get(i).expect("proof is incomplete");
            transcript.append_serializable_element(b"prover msg", prover_msg)?;
            verify_round_and_update_state(&mut verifier_state, prover_msg, transcript)?;
        }

        let subclaim = check_and_generate_subclaim(&verifier_state, &sum)?;

        end_timer!(start);
        Ok(subclaim)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compressed_sigma::encoding::{vec_to_mle_field, vec_to_mle_group};
    use crate::utils::hypercube::BooleanHypercube;
    use ark_ec::Group;
    use ark_ff::{Field, UniformRand};
    use ark_std::ops::Mul;
    use ark_std::{test_rng, One, Zero};
    use ark_test_curves::secp256k1::{Fr, G1Projective};
    use transcript::IOPTranscript;

    fn sum_over_hypercube(poly: &VirtualGroupPolynomialMixed<G1Projective>) -> G1Projective {
        let mut acc = G1Projective::zero();
        for y in BooleanHypercube::<Fr>::new(poly.num_variables) {
            acc += poly.evaluate(&y).unwrap();
        }
        acc
    }

    #[test]
    fn sumcheck_mixed_scalar_only() {
        let mut rng = test_rng();
        let n = 2usize;
        let s_vals: Vec<Fr> = (0..(1usize << n)).map(|_| Fr::rand(&mut rng)).collect();
        let s_mle = vec_to_mle_field(n, &s_vals);

        let g = G1Projective::generator().mul(Fr::rand(&mut rng));
        let mut poly = VirtualGroupPolynomialMixed::new(n);
        let s_idx = poly.add_scalar_mle(std::sync::Arc::new(s_mle)).unwrap();
        poly.add_product(None, vec![s_idx], g).unwrap();

        let sum = sum_over_hypercube(&poly);

        let mut prover_transcript = IOPTranscript::<Fr>::new(b"sumcheck-mixed");
        let proof = <() as GroupSumCheckMixed<G1Projective>>::prove(&poly, &mut prover_transcript).unwrap();

        let first_msg = &proof.proofs[0];
        assert_eq!(first_msg.evaluations[0] + first_msg.evaluations[1], sum);

        // manual interpolation check for round 1 -> round 2 consistency
        let r1 = proof.point[0];
        let expected_next = lagrange_eval_group(&first_msg.evaluations, r1);
        let second_msg_sum = proof.proofs[1].evaluations[0] + proof.proofs[1].evaluations[1];
        assert_eq!(expected_next, second_msg_sum);

        let mut verifier_transcript = IOPTranscript::<Fr>::new(b"sumcheck-mixed");
        let subclaim = <() as GroupSumCheckMixed<G1Projective>>::verify(
            sum,
            &proof,
            &poly.aux_info(),
            &mut verifier_transcript,
        )
        .unwrap();

        assert_eq!(
            poly.evaluate(&subclaim.point).unwrap(),
            subclaim.expected_evaluation
        );
    }

    #[test]
    fn sumcheck_mixed_group_times_scalar() {
        let mut rng = test_rng();
        let n = 2usize;
        let s_vals: Vec<Fr> = (0..(1usize << n)).map(|_| Fr::rand(&mut rng)).collect();
        let s_mle = vec_to_mle_field(n, &s_vals);

        let g_vals: Vec<G1Projective> = (0..(1usize << n))
            .map(|_| G1Projective::generator().mul(Fr::rand(&mut rng)))
            .collect();
        let g_mle = vec_to_mle_group(n, &g_vals);

        let mut poly = VirtualGroupPolynomialMixed::new(n);
        let s_idx = poly.add_scalar_mle(std::sync::Arc::new(s_mle)).unwrap();
        let g_idx = poly.add_group_mle(std::sync::Arc::new(g_mle)).unwrap();
        poly.add_product(Some(g_idx), vec![s_idx], G1Projective::zero())
            .unwrap();

        let sum = sum_over_hypercube(&poly);

        let mut prover_transcript = IOPTranscript::<Fr>::new(b"sumcheck-mixed");
        let proof = <() as GroupSumCheckMixed<G1Projective>>::prove(&poly, &mut prover_transcript).unwrap();

        let first_msg = &proof.proofs[0];
        assert_eq!(first_msg.evaluations[0] + first_msg.evaluations[1], sum);

        let r1 = proof.point[0];
        let expected_next = lagrange_eval_group(&first_msg.evaluations, r1);
        let second_msg_sum = proof.proofs[1].evaluations[0] + proof.proofs[1].evaluations[1];
        assert_eq!(expected_next, second_msg_sum);

        let mut verifier_transcript = IOPTranscript::<Fr>::new(b"sumcheck-mixed");
        let subclaim = <() as GroupSumCheckMixed<G1Projective>>::verify(
            sum,
            &proof,
            &poly.aux_info(),
            &mut verifier_transcript,
        )
        .unwrap();

        assert_eq!(
            poly.evaluate(&subclaim.point).unwrap(),
            subclaim.expected_evaluation
        );
    }

    fn lagrange_eval_group(evals: &[G1Projective], r: Fr) -> G1Projective {
        let len = evals.len();
        let mut acc = G1Projective::zero();
        for i in 0..len {
            let mut num = Fr::one();
            let mut den = Fr::one();
            for j in 0..len {
                if i == j {
                    continue;
                }
                num *= r - Fr::from(j as u64);
                den *= Fr::from(i as u64) - Fr::from(j as u64);
            }
            acc += evals[i].mul(num * den.inverse().unwrap());
        }
        acc
    }
}
