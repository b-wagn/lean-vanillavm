# Vanilla zkVM — Lean formalization

A Lean 4 / Mathlib formalization of the **Vanilla zkVM** and its main security result, ported from
the Ethereum Foundation zkVM whitepaper example (`zkvm-whitepaper/sampleVM/`, chapters ch01–ch05).
The goal is to formalize **correct-trace extractability (CTE)** — that an accepting final proof lets
an extractor recover a full, valid execution trace — for a recursive zkVM with committed memory and
a bus, reducing security to explicit cryptographic hardness assumptions.

The exact paper source used for review is pinned in
[`docs/PAPER_REVISION.md`](docs/PAPER_REVISION.md); this matters because the default paper branch and
its corrected `proof` revision currently differ on whether the step count `T` is adversary-chosen.

> **Status: WIP.** The current core is small, clean, and axiom-clean, but idealized (see
> [Idealization](#idealization)). The path from here to the full theorem is [`docs/PLAN.md`](docs/PLAN.md).

---

## Current architecture

TODO: explain the structure of the repository / codebase. Just briefly, explain sanity files role in one sentence

## Idealization

The crypto layer is **perfect / probability-free**.
Currently, cryptographic building blocks are idealized as *perfect* to simplify everything.
For instance, collision-resistance is just defined as being injective; knowledge
soundness is `∃ extractor, ∀ accepting (x,p), witness valid`; There is no security parameter, no `negl`, no running time yet.
The paper itself flags a deeper caveat (`rem:idealized`): straight-line
extraction composed across recursion layers needs "relativized" SNARKs, which provably don't exist,
so even the paper's bounds validate reduction **structure**, not a concrete security level.

We are of course aware that this if far from being cryptographically accurate, and we may change this in the future.



## Build

```bash
lake exe cache get
lake build
```

Requires the toolchain pinned in `lean-toolchain` and Mathlib `v4.32.0-rc1` (see `lakefile.toml`).
Every PR must keep `lake build` green and satisfy `#print axioms` ⊆ `{propext, Classical.choice,
Quot.sound}`.

## Contributing
TBD