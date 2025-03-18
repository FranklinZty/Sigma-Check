# Sigma-Check: Compressed Sigma Protocol from Sumcheck
This is a proof-of-concept implementation of a compressed sigma protocol from sumchecks.
The protocol take k instances, each with m-length witnesses satisfying d-degree polynomil relation h.

## Sumcheck on Group
The core building block for realizing such protocol is a modified sumcheck protocol for multilinear polynomials with group coefficients.
This block mainly refers to the HyperPlonk developed by Espresso System and is built on top of the Arkworks libraries including ark-ff, ark-ec and ark-poly.

## Amortization with Sumcheck on Field
First, “Amortization” technique (implemented in sumcheck on field) is employed to randomly combine all high-degree instances into a folded one without introduing an extra linearization process.

## Compression with Sumcheck on Group
Second, a “compression” technique (implemented in sumcheck on group) is applied, which achieves a logarithmic communication overhead for the verification of the folded instance.

## Building & Running
As usual, you can run the project using `cargo run`.
