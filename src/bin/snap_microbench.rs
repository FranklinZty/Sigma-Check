use ark_ec::Group;
use ark_ff::{One, UniformRand, Zero};
use ark_serialize::{CanonicalSerialize, Compress};
use ark_std::ops::Mul;
use ark_test_curves::secp256k1::{Fr, G1Projective};
use std::env;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;
use transcript::IOPTranscript;

use sumcheck_on_g::compressed_sigma::poly::{poly_prove, poly_verify, PolyProof};
use sumcheck_on_g::compressed_sigma::relations::{
    DensePoly, PolyMap, RPolyInstance, RPolyParams, RPolyWitness,
};

#[derive(Clone, Copy, Debug)]
enum BenchMode {
    Amort,
    Comp,
    Both,
}

#[derive(Clone, Debug)]
struct BenchConfig {
    runs: usize,
    exp_min: u32,
    exp_max: u32,
    degrees: Vec<usize>,
    mode: BenchMode,
    compare: bool,
    optimized: Option<bool>,
    csv: bool,
    out_path: Option<PathBuf>,
    fixed_k: usize,
    fixed_m: usize,
}

#[derive(Clone, Debug)]
struct BenchRow {
    regime: &'static str,
    optimized: bool,
    degree: usize,
    k: usize,
    m: usize,
    prove_ms: f64,
    verify_ms: f64,
    proof_bytes: usize,
}

fn main() {
    let config = parse_args();
    let field_bytes = Fr::zero().serialized_size(Compress::Yes);
    let group_bytes = G1Projective::generator().serialized_size(Compress::No);

    let rows = run_benchmarks(&config, field_bytes, group_bytes);

    if config.csv {
        let mut csv = String::new();
        csv.push_str("regime,optimized,degree,k,m,prover_ms,verifier_ms,proof_bytes\n");
        for row in &rows {
            csv.push_str(&format!(
                "{},{},{},{},{},{:.6},{:.6},{}\n",
                row.regime,
                if row.optimized { "opt" } else { "no_opt" },
                row.degree,
                row.k,
                row.m,
                row.prove_ms,
                row.verify_ms,
                row.proof_bytes
            ));
        }
        print!("{}", csv);
        if let Some(path) = &config.out_path {
            if let Err(err) = fs::write(path, csv.as_bytes()) {
                eprintln!("failed to write {}: {}", path.display(), err);
            }
        }
    } else {
        print_human(&rows, field_bytes, group_bytes, &config);
    }
}

fn parse_args() -> BenchConfig {
    let mut runs = 100usize;
    let mut exp_min = 1u32;
    let mut exp_max = 10u32;
    let mut degrees = vec![1usize, 2, 4];
    let mut mode = BenchMode::Both;
    let mut compare = false;
    let mut optimized = None;
    let mut csv = false;
    let mut out_path = None;
    let mut fixed_k = 128usize;
    let mut fixed_m = 128usize;

    let mut args = env::args().skip(1);
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--runs" => {
                let v = args.next().expect("--runs expects a value");
                runs = v.parse().expect("invalid --runs");
            }
            "--exp-min" => {
                let v = args.next().expect("--exp-min expects a value");
                exp_min = v.parse().expect("invalid --exp-min");
            }
            "--exp-max" => {
                let v = args.next().expect("--exp-max expects a value");
                exp_max = v.parse().expect("invalid --exp-max");
            }
            "--deg" => {
                let v = args.next().expect("--deg expects a value");
                degrees = v
                    .split(',')
                    .filter(|s| !s.trim().is_empty())
                    .map(|s| s.trim().parse::<usize>().expect("invalid degree"))
                    .collect();
            }
            "--mode" => {
                let v = args.next().expect("--mode expects a value");
                mode = match v.as_str() {
                    "amort" => BenchMode::Amort,
                    "comp" => BenchMode::Comp,
                    "both" => BenchMode::Both,
                    _ => panic!("invalid --mode (amort|comp|both)"),
                };
            }
            "--optimized" => optimized = Some(true),
            "--unoptimized" => optimized = Some(false),
            "--compare" => compare = true,
            "--csv" => csv = true,
            "--out" => {
                let v = args.next().expect("--out expects a path");
                out_path = Some(PathBuf::from(v));
            }
            "--k-fixed" => {
                let v = args.next().expect("--k-fixed expects a value");
                fixed_k = v.parse().expect("invalid --k-fixed");
            }
            "--m-fixed" => {
                let v = args.next().expect("--m-fixed expects a value");
                fixed_m = v.parse().expect("invalid --m-fixed");
            }
            "--help" => {
                print_usage();
                std::process::exit(0);
            }
            _ => panic!("unknown argument: {}", arg),
        }
    }

    if exp_min > exp_max {
        panic!("exp-min must be <= exp-max");
    }
    if runs == 0 {
        panic!("runs must be > 0");
    }
    if degrees.is_empty() {
        panic!("degree list is empty");
    }

    BenchConfig {
        runs,
        exp_min,
        exp_max,
        degrees,
        mode,
        compare,
        optimized,
        csv,
        out_path,
        fixed_k,
        fixed_m,
    }
}

fn print_usage() {
    println!("snap_microbench options:");
    println!("  --runs N           number of runs per data point (default: 100)");
    println!("  --exp-min N        min exponent for k/m (default: 1 -> 2^1)");
    println!("  --exp-max N        max exponent for k/m (default: 10 -> 2^10)");
    println!("  --deg list         comma list of degrees (default: 1,2,4)");
    println!("  --mode amort|comp|both (default: both)");
    println!("  --optimized        run optimized amortization");
    println!("  --unoptimized      run unoptimized amortization");
    println!("  --compare          run both optimized and unoptimized");
    println!("  --k-fixed N        fixed k for compression regime (default: 128)");
    println!("  --m-fixed N        fixed m for amortization regime (default: 128)");
    println!("  --csv              output CSV to stdout");
    println!("  --out PATH         write CSV to PATH (requires --csv)");
}

fn run_benchmarks(config: &BenchConfig, field_bytes: usize, group_bytes: usize) -> Vec<BenchRow> {
    let mut rows = Vec::new();
    let mut rng = ark_std::test_rng();

    let opt_modes: Vec<bool> = if config.compare {
        vec![false, true]
    } else {
        vec![config.optimized.unwrap_or(true)]
    };

    for &degree in &config.degrees {
        if matches!(config.mode, BenchMode::Amort | BenchMode::Both) {
            let m = config.fixed_m;
            let params = sample_params(&mut rng, m, degree);
            for exp in config.exp_min..=config.exp_max {
                let k = 1usize << exp;
                let (instances, witnesses) = sample_instances(&mut rng, &params, k);
                for &optimized in &opt_modes {
                    let result = bench_instance(
                        &params,
                        &instances,
                        &witnesses,
                        optimized,
                        config.runs,
                        field_bytes,
                        group_bytes,
                    );
                    rows.push(BenchRow {
                        regime: "amort",
                        optimized,
                        degree,
                        k,
                        m,
                        prove_ms: result.prove_ms,
                        verify_ms: result.verify_ms,
                        proof_bytes: result.proof_bytes,
                    });
                }
            }
        }

        if matches!(config.mode, BenchMode::Comp | BenchMode::Both) {
            let k = config.fixed_k;
            for exp in config.exp_min..=config.exp_max {
                let m = 1usize << exp;
                let params = sample_params(&mut rng, m, degree);
                let (instances, witnesses) = sample_instances(&mut rng, &params, k);
                for &optimized in &opt_modes {
                    let result = bench_instance(
                        &params,
                        &instances,
                        &witnesses,
                        optimized,
                        config.runs,
                        field_bytes,
                        group_bytes,
                    );
                    rows.push(BenchRow {
                        regime: "comp",
                        optimized,
                        degree,
                        k,
                        m,
                        prove_ms: result.prove_ms,
                        verify_ms: result.verify_ms,
                        proof_bytes: result.proof_bytes,
                    });
                }
            }
        }
    }

    rows
}

#[derive(Clone, Copy, Debug)]
struct BenchResult {
    prove_ms: f64,
    verify_ms: f64,
    proof_bytes: usize,
}

fn bench_instance(
    params: &RPolyParams<G1Projective>,
    instances: &[RPolyInstance<G1Projective>],
    witnesses: &[RPolyWitness<G1Projective>],
    optimized: bool,
    runs: usize,
    field_bytes: usize,
    group_bytes: usize,
) -> BenchResult {
    let mut prove_total = 0.0;
    let mut verify_total = 0.0;
    let mut proof_total = 0usize;

    for _ in 0..runs {
        let mut prover_transcript = IOPTranscript::<Fr>::new(b"SnapSigma transcript");
        let prove_start = Instant::now();
        let proof = poly_prove(params, instances, witnesses, optimized, &mut prover_transcript)
            .expect("poly_prove failed");
        prove_total += prove_start.elapsed().as_secs_f64() * 1000.0;

        let proof_bytes = poly_proof_size_bytes(&proof, params.g_vec.len(), field_bytes, group_bytes);
        proof_total += proof_bytes;

        let mut verifier_transcript = IOPTranscript::<Fr>::new(b"SnapSigma transcript");
        let verify_start = Instant::now();
        poly_verify(params, instances, &proof, optimized, &mut verifier_transcript)
            .expect("poly_verify failed");
        verify_total += verify_start.elapsed().as_secs_f64() * 1000.0;
    }

    BenchResult {
        prove_ms: prove_total / runs as f64,
        verify_ms: verify_total / runs as f64,
        proof_bytes: proof_total / runs,
    }
}

fn sample_params(
    rng: &mut impl rand::Rng,
    m: usize,
    degree: usize,
) -> RPolyParams<G1Projective> {
    let mut g_vec = Vec::with_capacity(m);
    for _ in 0..m {
        g_vec.push(G1Projective::generator().mul(Fr::rand(rng)));
    }

    let mut coeffs = Vec::with_capacity(degree + 1);
    for _ in 0..=degree {
        coeffs.push(Fr::rand(rng));
    }
    if coeffs.last().map(|c| c.is_zero()).unwrap_or(true) {
        let last = coeffs.last_mut().expect("degree+1 coeffs");
        *last = Fr::one();
    }
    let h = DensePoly::new(coeffs);

    RPolyParams { g_vec, h }
}

fn sample_instances(
    rng: &mut impl rand::Rng,
    params: &RPolyParams<G1Projective>,
    k: usize,
) -> (Vec<RPolyInstance<G1Projective>>, Vec<RPolyWitness<G1Projective>>) {
    let m = params.g_vec.len();
    let mut instances = Vec::with_capacity(k);
    let mut witnesses = Vec::with_capacity(k);

    for _ in 0..k {
        let mut f = Vec::with_capacity(m);
        for _ in 0..m {
            f.push(Fr::rand(rng));
        }

        let mut commitment = G1Projective::zero();
        for (g_i, f_i) in params.g_vec.iter().zip(f.iter()) {
            commitment += g_i.mul(*f_i);
        }
        let v = f.iter().map(|fi| params.h.eval(*fi)).collect::<Vec<_>>();

        instances.push(RPolyInstance { F: commitment, v });
        witnesses.push(RPolyWitness { f });
    }

    (instances, witnesses)
}

fn poly_proof_size_bytes(
    proof: &PolyProof<G1Projective>,
    m: usize,
    field_bytes: usize,
    group_bytes: usize,
) -> usize {
    let mut total = 0usize;

    // mask instance
    total += group_bytes; // F
    total += m * field_bytes; // v

    // amort proof: g2 sumcheck
    total += field_sumcheck_size(&proof.amort_proof.g2_proof);
    total += field_bytes; // s

    if let Some(g1_proof) = &proof.amort_proof.g1_proof {
        total += group_sumcheck_size(g1_proof);
    }
    if proof.amort_proof.F.is_some() {
        total += group_bytes;
    }

    // comp proof
    total += mixed_sumcheck_size(&proof.comp_proof.sumcheck_proof);
    total += field_bytes; // f_ry

    total
}

fn field_sumcheck_size(proof: &sumcheck_on_g::sumcheck::structs::IOPProof<Fr>) -> usize {
    let point_bytes: usize = proof
        .point
        .iter()
        .map(|p| p.serialized_size(Compress::Yes))
        .sum();
    let msg_bytes: usize = proof
        .proofs
        .iter()
        .map(|m| m.serialized_size(Compress::Yes))
        .sum();
    point_bytes + msg_bytes
}

fn group_sumcheck_size(
    proof: &sumcheck_on_g::sumcheckg::structs::IOPProof<G1Projective>,
) -> usize {
    let point_bytes: usize = proof
        .point
        .iter()
        .map(|p| p.serialized_size(Compress::Yes))
        .sum();
    let msg_bytes: usize = proof
        .proofs
        .iter()
        .map(|m| m.serialized_size(Compress::No))
        .sum();
    point_bytes + msg_bytes
}

fn mixed_sumcheck_size(
    proof: &sumcheck_on_g::sumcheckg_mixed::structs::IOPProof<G1Projective>,
) -> usize {
    let point_bytes: usize = proof
        .point
        .iter()
        .map(|p| p.serialized_size(Compress::Yes))
        .sum();
    let msg_bytes: usize = proof
        .proofs
        .iter()
        .map(|m| m.serialized_size(Compress::No))
        .sum();
    point_bytes + msg_bytes
}

fn print_human(rows: &[BenchRow], field_bytes: usize, group_bytes: usize, config: &BenchConfig) {
    println!("Snap×Snap microbench");
    println!(
        "runs={}, exp=[{}..={}], degrees={:?}, fixed_k={}, fixed_m={}, field_bytes={}, group_bytes={}",
        config.runs,
        config.exp_min,
        config.exp_max,
        config.degrees,
        config.fixed_k,
        config.fixed_m,
        field_bytes,
        group_bytes
    );

    let mut rows_sorted = rows.to_vec();
    rows_sorted.sort_by_key(|r| (r.regime, r.degree, r.optimized, r.k, r.m));

    for row in rows_sorted {
        println!(
            "{} | d={} | opt={} | k={} | m={} | prove={:.3} ms | verify={:.3} ms | proof={} bytes",
            row.regime,
            row.degree,
            row.optimized,
            row.k,
            row.m,
            row.prove_ms,
            row.verify_ms,
            row.proof_bytes
        );
    }
}
