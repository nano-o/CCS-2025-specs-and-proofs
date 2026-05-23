# Formal specifications and proofs for the paper "Optimistic, Signature-Free Reliable Broadcast and Its Applications", CCS 2025

The paper is available at the following link: ["Optimistic, Signature-Free Reliable Broadcast and Its Applications"](https://arxiv.org/abs/2505.02761).

Note that, in versions `v3` and earlier (`v3` is the arXiv paper version), the optimistic RBC protocol has a liveness issue.
Version `v4` fixes the issue.
Additionally, to rule out any remaining issue, we have written a mechanically-checked proof of both the safety and liveness of the optimistic RBC protocol.
This proof uses the Ivy prover and the Isabelle/HOL proof assistant (see below).

## Docker image

A [Dockerfile](./Dockerfile) is provided that bundles Java/TLC, Ivy, and Isabelle in a single image so all the artifacts in this repo can be checked without installing anything locally.

A pre-built image is published to Docker Hub:

```bash
docker pull giulianolosa/ccs2025-artifact:latest
docker run --rm -it giulianolosa/ccs2025-artifact:latest
```

To build the image yourself instead:

```bash
docker build -t ccs2025-artifact .
docker run --rm -it ccs2025-artifact
```

Inside the container, from `/artifact`:

- `make check-ivy` -- check the Ivy proof.
- `make check-isabelle` -- check the Isabelle proofs.
- `make run-tlc TLA_SPEC=TLCSailfish1.tla` -- run TLC on a TLA+ spec (see below).

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

A PlusCal/TLA+ specification appears in [TwoStepOptimiticBroadcast.tla](./TwoStepOptimiticBroadcast.tla).

### Ivy and Isabelle/HOL specifications and mechanically-checked proofs

We show 3 properties of the optimistic RBC protocol:
- No two non-faulty parties disagree on the committed value (see invariant `agreement` in [opti_rbc.ivy](./opti_rbc.ivy)).
- If the broadcaster is non-faulty, then eventually all non-faulty parties commit its value (see action `check_validity` in [opti_rbc.ivy](./opti_rbc.ivy)).
- If a non-faulty party commits, then eventually all non-faulty parties commit (see action `check_totality` in [opti_rbc.ivy](./opti_rbc.ivy)).

The proof has two parts: an Ivy proof based on an abstract model in [opti_rbc.ivy](./opti_rbc.ivy), and a separate proof in Isabelle/HOL that the abstract model is sound in [OptiRBC/AxiomaticDomainModel.thy](./OptiRBC/AxiomaticDomainModel.thy).
The safety-proof methodology is comparable to the methodology of the paper [Verification of Threshold-Based Distributed Algorithms by Decomposition to Decidable Logics](https://arxiv.org/abs/1905.07805), except that the BAPA part was done in Isabelle/HOL.

You can browse the Isabelle proofs online:
[AbstractDomainModel](https://htmlpreview.github.io/?https://raw.githubusercontent.com/nano-o/CCS-2025-specs-and-proofs/main/OptiRBC/browser_info/AbstractDomainModel.html) and
[AxiomaticDomainModel](https://htmlpreview.github.io/?https://raw.githubusercontent.com/nano-o/CCS-2025-specs-and-proofs/main/OptiRBC/browser_info/AxiomaticDomainModel.html).
A typeset PDF of the theories is also available: [document.pdf](./OptiRBC/browser_info/document.pdf).

#### Checking the Ivy proof

Install [Ivy](https://github.com/kenmcmil/ivy) in a Python 3 virtual environment and check the proof:

```bash
git clone https://github.com/kenmcmil/ivy.git
python3 -m venv ivy-venv
source ivy-venv/bin/activate
cd ivy
pip install -e .
cd ..
ivy_check seed=$RANDOM opti_rbc.ivy
```

If it takes too long then just restart `ivy_check`; you might get luckier with the next random seed.

#### Checking the Isabelle proof

Install Isabelle and then open [OptiRBC/AbstractDomainModel.thy](./OptiRBC/AbstractDomainModel.thy) and [OptiRBC/AxiomaticDomainModel.thy](./OptiRBC/AxiomaticDomainModel.thy).
`AbstractDomainModel` defines the abstract model, and `AxiomaticDomainModel` shows that the axiomatic model based on thresholds satisfies all the properties of the abstract model.

The session is described in [OptiRBC/ROOT](./OptiRBC/ROOT); to build it from the command line, run `isabelle build -D OptiRBC` from the repository root.
To also produce the typeset PDF at `./OptiRBC/output/document.pdf`, pass `-o document=pdf` (this requires a LaTeX toolchain with LuaLaTeX): `isabelle build -o document=pdf -D OptiRBC`.

#### Regenerating the HTML previews and the PDF

The contents of [OptiRBC/browser_info/](./OptiRBC/browser_info/) (the HTML files behind the `htmlpreview.github.io` links above, plus `document.pdf`) are generated by Isabelle's presentation output. To regenerate them after editing the theories, run the following from the repository root:

```bash
isabelle build -o document=pdf -P /tmp/optirbc_browser -D OptiRBC
cp /tmp/optirbc_browser/Unsorted/OptiRBC/*.html \
   /tmp/optirbc_browser/Unsorted/OptiRBC/*.css \
   /tmp/optirbc_browser/Unsorted/OptiRBC/*.pdf \
   OptiRBC/browser_info/
```

`-P` writes the presentation tree (`<group>/<session>/`) to the given directory; since `ROOT` does not set a group, the session lands under `Unsorted/OptiRBC/`. `-o document=pdf` enables PDF generation (requires a LaTeX toolchain with LuaLaTeX). The `cp` line picks up both the HTML pages and `document.pdf`. Commit the refreshed files in `OptiRBC/browser_info/` so the links keep working.

## License

Copyright 2026 Stellar Development Foundation. Licensed under the Apache License, Version 2.0; see [LICENSE](./LICENSE) and [NOTICE](./NOTICE).
