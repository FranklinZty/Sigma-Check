pub mod errors;
pub mod group_multilinear_extension;
pub mod multilinear_group_polynomial;
pub mod multilinear_polynomial;
pub mod compressed_sigma;
pub mod sumcheckg_mixed;
pub mod sumcheck;
pub mod sumcheckg;
pub mod utils;
pub mod virtual_group_polynomial;
pub mod virtual_group_polynomial_mixed;
pub mod virtual_polynomial;

use crate::sumcheck::{structs::IOPProof as FieldProof, SumCheck};
use crate::sumcheckg::{structs::IOPProof as GroupProof, GroupSumCheck};
use crate::utils::hypercube::BooleanHypercube;
use crate::virtual_group_polynomial::VirtualGroupPolynomial;
use crate::virtual_polynomial::VirtualPolynomial;
use ark_ec::Group;
use ark_ff::{One, UniformRand, Zero};
use ark_poly::DenseMultilinearExtension;
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::ops::Mul;
use ark_std::rand::Rng;
use ark_test_curves::secp256k1::{Fr, G1Projective};
use std::env;
use std::sync::Arc;
use std::time::Instant;
use subroutines::PolyIOP;

#[derive(Clone, Copy, Debug, Default)]
struct BenchmarkStats {
    prove_ms: f64,
    proof_bytes: usize,
    verify_ms: f64,
}

fn main() {
    let (num_vars, rounds, csv_mode) = parse_cli_args();

    let field_stats = benchmark_field_sumcheck(num_vars, rounds);
    let group_stats = benchmark_group_sumcheck(num_vars, rounds);

    if csv_mode {
        println!(
            "num_vars,rounds,field_prove_ms,field_proof_bytes,field_verify_ms,group_prove_ms,group_proof_bytes,group_verify_ms"
        );
        println!(
            "{},{},{:.6},{},{:.6},{:.6},{},{:.6}",
            num_vars,
            rounds,
            field_stats.prove_ms,
            field_stats.proof_bytes,
            field_stats.verify_ms,
            group_stats.prove_ms,
            group_stats.proof_bytes,
            group_stats.verify_ms
        );
    } else {
        println!(
            "Sumcheck benchmark (num_vars={}, rounds={})",
            num_vars, rounds
        );
        println!(
            "Field: prove={:.3} ms, proof_len={} bytes, verify={:.3} ms",
            field_stats.prove_ms, field_stats.proof_bytes, field_stats.verify_ms
        );
        println!(
            "Group: prove={:.3} ms, proof_len={} bytes, verify={:.3} ms",
            group_stats.prove_ms, group_stats.proof_bytes, group_stats.verify_ms
        );
    }
}

fn parse_cli_args() -> (usize, usize, bool) {
    let raw_args = env::args().skip(1).collect::<Vec<_>>();
    let mut csv_mode = false;
    let mut positional = Vec::new();
    for arg in raw_args {
        if arg == "--csv" {
            csv_mode = true;
        } else {
            positional.push(arg);
        }
    }

    let (num_vars, rounds) = match positional.as_slice() {
        [] => (8, 20),
        [num_vars, rounds] => {
            let num_vars = num_vars.parse::<usize>().unwrap_or_else(|_| {
                panic!("invalid num_vars: '{}', expected positive integer", num_vars)
            });
            let rounds = rounds.parse::<usize>().unwrap_or_else(|_| {
                panic!("invalid rounds: '{}', expected positive integer", rounds)
            });
            assert!(num_vars > 0, "num_vars must be > 0");
            assert!(rounds > 0, "rounds must be > 0");
            (num_vars, rounds)
        }
        _ => panic!("usage: cargo run -- [--csv] <num_vars> <rounds>"),
    };

    (num_vars, rounds, csv_mode)
}

fn benchmark_field_sumcheck(num_vars: usize, rounds: usize) -> BenchmarkStats {
    let mut rng = ark_std::test_rng();
    let mut prove_total_ms = 0.0;
    let mut verify_total_ms = 0.0;
    let mut proof_total_bytes = 0usize;

    for _ in 0..rounds {
        let poly = sample_field_poly(num_vars, &mut rng);
        let claimed_sum = sum_field_over_hypercube(&poly);

        let mut prover_transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
        let prove_start = Instant::now();
        let proof = <PolyIOP<Fr> as SumCheck<Fr>>::prove(&poly, &mut prover_transcript).unwrap();
        prove_total_ms += prove_start.elapsed().as_secs_f64() * 1000.0;
        proof_total_bytes += field_proof_size_bytes(&proof);

        let mut verifier_transcript = <PolyIOP<Fr> as SumCheck<Fr>>::init_transcript();
        let verify_start = Instant::now();
        let subclaim = <PolyIOP<Fr> as SumCheck<Fr>>::verify(
            claimed_sum,
            &proof,
            &poly.aux_info,
            &mut verifier_transcript,
        )
        .unwrap();
        verify_total_ms += verify_start.elapsed().as_secs_f64() * 1000.0;

        assert_eq!(
            poly.evaluate(&subclaim.point).unwrap(),
            subclaim.expected_evaluation
        );
    }

    BenchmarkStats {
        prove_ms: prove_total_ms / rounds as f64,
        proof_bytes: proof_total_bytes / rounds,
        verify_ms: verify_total_ms / rounds as f64,
    }
}

fn benchmark_group_sumcheck(num_vars: usize, rounds: usize) -> BenchmarkStats {
    let mut rng = ark_std::test_rng();
    let mut prove_total_ms = 0.0;
    let mut verify_total_ms = 0.0;
    let mut proof_total_bytes = 0usize;

    for _ in 0..rounds {
        let poly = sample_group_poly(num_vars, &mut rng);
        let claimed_sum = sum_group_over_hypercube(&poly);

        let mut prover_transcript = <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::init_transcript();
        let prove_start = Instant::now();
        let proof =
            <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::prove(&poly, &mut prover_transcript)
                .unwrap();
        prove_total_ms += prove_start.elapsed().as_secs_f64() * 1000.0;
        proof_total_bytes += group_proof_size_bytes(&proof);

        let mut verifier_transcript =
            <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::init_transcript();
        let verify_start = Instant::now();
        let subclaim = <PolyIOP<Fr> as GroupSumCheck<G1Projective>>::verify(
            claimed_sum,
            &proof,
            &poly.aux_info,
            &mut verifier_transcript,
        )
        .unwrap();
        verify_total_ms += verify_start.elapsed().as_secs_f64() * 1000.0;

        assert_eq!(
            poly.evaluate(&subclaim.point).unwrap(),
            subclaim.expected_evaluation
        );
    }

    BenchmarkStats {
        prove_ms: prove_total_ms / rounds as f64,
        proof_bytes: proof_total_bytes / rounds,
        verify_ms: verify_total_ms / rounds as f64,
    }
}

fn field_proof_size_bytes(proof: &FieldProof<Fr>) -> usize {
    let point_size = proof.point.serialized_size(Compress::Yes);
    let msgs_size = proof
        .proofs
        .iter()
        .map(|msg| msg.serialized_size(Compress::Yes))
        .sum::<usize>();
    point_size + msgs_size
}

fn group_proof_size_bytes(proof: &GroupProof<G1Projective>) -> usize {
    let point_size = proof.point.serialized_size(Compress::Yes);
    let msgs_size = proof
        .proofs
        .iter()
        .map(|msg| msg.serialized_size(Compress::Yes))
        .sum::<usize>();
    point_size + msgs_size
}

fn random_scalar_mle<R: Rng>(num_vars: usize, rng: &mut R) -> Arc<DenseMultilinearExtension<Fr>> {
    let evals = (0..(1usize << num_vars))
        .map(|_| Fr::rand(rng))
        .collect::<Vec<_>>();
    Arc::new(DenseMultilinearExtension::from_evaluations_vec(
        num_vars, evals,
    ))
}

fn sample_field_poly<R: Rng>(num_vars: usize, rng: &mut R) -> VirtualPolynomial<Fr> {
    let mle1 = random_scalar_mle(num_vars, rng);
    let mle2 = random_scalar_mle(num_vars, rng);
    let mle3 = random_scalar_mle(num_vars, rng);

    let mut poly = VirtualPolynomial::new_from_mle(&mle1, Fr::rand(rng));
    poly.mul_by_mle(mle2, Fr::one()).unwrap();
    poly.add_mle_list(vec![mle3], Fr::rand(rng)).unwrap();
    poly
}

fn sample_group_poly<R: Rng>(num_vars: usize, rng: &mut R) -> VirtualGroupPolynomial<G1Projective> {
    let mle1 = random_scalar_mle(num_vars, rng);
    let mle2 = random_scalar_mle(num_vars, rng);
    let mle3 = random_scalar_mle(num_vars, rng);
    let base = G1Projective::generator();

    let mut poly = VirtualGroupPolynomial::new_from_mle(&mle1, base.mul(Fr::rand(rng)));
    poly.mul_by_mle(mle2, Fr::one()).unwrap();
    poly.add_mle_list(vec![mle3], base.mul(Fr::rand(rng)))
        .unwrap();
    poly
}

fn sum_field_over_hypercube(poly: &VirtualPolynomial<Fr>) -> Fr {
    let mut sum = Fr::zero();
    for point in BooleanHypercube::<Fr>::new(poly.aux_info.num_variables) {
        sum += poly.evaluate(&point).unwrap();
    }
    sum
}

fn sum_group_over_hypercube(poly: &VirtualGroupPolynomial<G1Projective>) -> G1Projective {
    let mut sum = G1Projective::zero();
    for point in BooleanHypercube::<Fr>::new(poly.aux_info.num_variables) {
        sum += poly.evaluate(&point).unwrap();
    }
    sum
}
