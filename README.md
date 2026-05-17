# Formal specifications and proofs for the paper "Optimistic, Signature-Free Reliable Broadcast and Its Applications", CCS 2025

The paper is available at the following link: ["Optimistic, Signature-Free Reliable Broadcast and Its Applications"](https://arxiv.org/abs/2505.02761).

Note that, in versions `v3` and earlier, the optimistic RBC protocol has a liveness issue.
Version `v4` fixes the issue.
Additionally, to rule out any possible remaining issue, we have mechanically-checked both the safety and liveness of the optimistic RBC protocol, for arbitrarily many parties and arbitrary long executions, using the Ivy prover and the Isabelle/HOL proof assistant (see below).

## PlusCal/TLA+ specification of Sailfish++

### Block DAGs

[BlockDag.tla](./BlockDag.tla) defines block DAGs and how DAG-based consensus protocols linearize them.
To run some basic tests, run `make block-dag-test`.

### Sailfish

[Sailfish.tla](./Sailfish.tla) contains a high-level formal specification modeling both Sailfish and Sailfish++ (at the level of abstraction of the specification, the differences between the protocols are not visible).

Sailfish is described in the paper ["Sailfish: Towards Improving the Latency of DAG-based BFT"](https://eprint.iacr.org/2024/472), S&P 2025.

To run the TLC model-checker on the specification, first translate the PlusCal part to TLA+ with `make trans TLA_SPEC=Sailfish.tla` and then run `make run-tlc TLA_SPEC=TLCSailfish1.tla`. The specification `TLCSailfish1.tla` and the associated config file `TLCSailfish1.cfg` fix a concrete system size and model-checking bounds and define what the properties to check (a basic type invariant, agreement, and liveness).
`TLCSailfish2.tla` and the associated config file `TLCSailfish2.cfg` use different bounds.

Have a look at the Makefile to tweak TLC options.

Notes:
- `make trans` rewrites the TLA+ module in place after PlusCal translation.
- The Makefile expects `java` and `wget` to be available to download and run `tla2tools.jar`.

## Optimistic Reliable Broadcast

### PlusCal/TLA+ specification

### Ivy and Isabelle/HOL specifications and mechanically-checked proofs
