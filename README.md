# Sigma-Check (Snap×Snap)

This repository contains a pedagogical Rust implementation of paper "Snap×Snap: Compressed Sigma Protocols from Sum-check".
Snap×Snap is a direct extension of compressed Σ-protocols to polynomial relations via two sumchecks.
A first sumcheck yields logarithmic amortization without linearization, with explicit
degree-dependent factors. Notably, skipping linearization may leave the folded relation
high-degree, for which Bulletproofs no longer fit. Crucially, a second sumcheck fills the
compression role, retaining polylogarithmic communication even when the folded relation remains
high-degree. Hence, Snap×Snap extends compressed Sigma-protocols beyond the homomorphic regime while
keeping a commitment-centric, Fiat–Shamir-friendly form.

## Implementation Highlights
- Field sumcheck and group sumcheck primitives.
- Mixed group sumcheck for polynomials with both scalar and group MLE factors.
- Compressed Sigma pipeline for polynomial relations:
  - RPoly relation.
  - ΠAmort (optimized and unoptimized variants).
  - ΠComp (compression via group-valued sumcheck).
  - ΠPoly (composition of ΠAmort and ΠComp).
- XY-ordered MLE encoding utilities for table-to-MLE conversion and evaluation helpers.

## Microbenchmark
Binary: `snap_microbench`

Example (paper-style settings):
```
cargo run --release --bin snap_microbench -- --runs 100 --exp-min 1 --exp-max 10 --deg 1,2,4 --mode both --csv --out tmp/bench/snap_microbench.csv
```

Output columns: `regime, optimized, degree, k, m, prover_ms, verifier_ms, proof_bytes`.
Proof size uses uncompressed group elements and 256-bit field elements (Arkworks serialization).

Latest run in this workspace (for quick iteration) was stored at:
`tmp/bench/snap_microbench.csv`

## Evaluation (Section 8.2)
Setup and methodology mirrored from the paper:
- Implementation in Rust using Arkworks; group-valued multilinear sumcheck for `ΠComp`.
- Fiat–Shamir via Merlin.
- Commitments use secp256k1.
- Metrics: prover time, verifier time, proof size in bytes (assume 256-bit field elements and uncompressed group elements).
- Two regimes:
  - Amortization: fix `m = 128`, vary `k = 2^1..2^10`.
  - Compression: fix `k = 128`, vary `m = 2^1..2^10`.
- Degrees: `d ∈ {1, 2, 4}`.
- Average over `runs` samples.

## Tests
```
cargo test -q sumcheck_mixed_
cargo test -q comp_roundtrip_small
```
