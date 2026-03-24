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

Part of the experimental results is given below:
| phase | degree | m | k | prove(s) | verify(s) | proof(KB) |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| amortization | 1 | 128 | 2 | 0.168935 | 0.010246 | 5.998047 |
| amortization | 1 | 128 | 4 | 0.173429 | 0.010543 | 6.130859 |
| amortization | 1 | 128 | 8 | 0.192985 | 0.011364 | 6.263672 |
| amortization | 1 | 128 | 16 | 0.198465 | 0.011849 | 6.396484 |
| compression | 1 | 2 | 128 | 0.012434 | 0.010214 | 1.480469 |
| compression | 1 | 4 | 128 | 0.016228 | 0.011068 | 1.772461 |
| compression | 1 | 8 | 128 | 0.022735 | 0.011477 | 2.126953 |
| compression | 1 | 16 | 128 | 0.036049 | 0.012539 | 2.606445 |
| amortization | 2 | 128 | 2 | 0.272843 | 0.011360 | 6.504883 |
| amortization | 2 | 128 | 4 | 0.279245 | 0.011292 | 6.668945 |
| amortization | 2 | 128 | 8 | 0.317879 | 0.012033 | 6.833008 |
| amortization | 2 | 128 | 16 | 0.322521 | 0.013048 | 6.997070 |
| compression | 2 | 2 | 128 | 0.014974 | 0.010971 | 1.793945 |
| compression | 2 | 4 | 128 | 0.020412 | 0.011027 | 2.149414 |
| compression | 2 | 8 | 128 | 0.032020 | 0.011566 | 2.567383 |
| compression | 2 | 16 | 128 | 0.055662 | 0.012530 | 3.110352 |
| amortization | 4 | 128 | 2 | 0.520929 | 0.011386 | 7.518555 |
| amortization | 4 | 128 | 4 | 0.567736 | 0.011667 | 7.745117 |
| amortization | 4 | 128 | 8 | 0.617251 | 0.012278 | 7.971680 |
| amortization | 4 | 128 | 16 | 0.668491 | 0.012754 | 8.198242 |
| compression | 4 | 2 | 128 | 0.020687 | 0.011013 | 2.420898 |
| compression | 4 | 4 | 128 | 0.034033 | 0.011496 | 2.903320 |
| compression | 4 | 8 | 128 | 0.059509 | 0.011646 | 3.448242 |
| compression | 4 | 16 | 128 | 0.110928 | 0.012844 | 4.118164 |

## Tests

```
cargo test -q sumcheck_mixed_
cargo test -q comp_roundtrip_small
```
