# zkVM Recursion in Lean
Note. This is **WIP**. This is *purely AI made* so far. Take everything not too seriously.


## Context and Goal
This repository contains a Lean formalization of a recursive zkVM architecture, ported from a [document](https://github.com/khovratovich/zkvm-ef-security-sprint/blob/3ec1c63846c4b852f723168aadfd8490e52529a5/vanillaVM-W1/w1-sample.pdf) produced as an example for the Ethereum Foundation's zkVM whitepaper guidelines.

The ultimate goal is to explore how to model and analyze security of recursion in Lean, despite the [theoretical obstacles of recursion security](https://eprint.iacr.org/2024/728.pdf).

## Idealization
Currently, cryptographic building blocks are idealized as *perfect* to simplify everything.
For instance, collision-resistance is just defined as being injective. 

We are of course aware that this if far from being cryptographically accurate, and we may change this in the future.

## Notes and Disclaimers
Things that are not done at all:
* actual recursion; so far it is just a two step proof: (1) prove each segment (2) merge these proofs

The `yl-memory-reconstruction` branch additionally contains a standalone,
kernel-checked committed-to-full-memory reconstruction layer:

* a named one-step reduction returning success or explicit position/update
  binding failures;
* a formal version of the verifier-ignored append-bit counterexample;
* a trace fold maintaining the commitment invariant and proving exact full
  initial/final boundaries;
* a definitionally connected Bus step and an end-to-end theorem from an
  accepting segment proof to a reconstructed full-memory segment trace.

See [`docs/MEMORY_RECONSTRUCTION.md`](docs/MEMORY_RECONSTRUCTION.md). This layer
is not yet integrated with the recursive/final extractor or a concrete
program/ISA, and it remains qualitative rather than computational.
