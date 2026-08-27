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

```
VanillaZkVM/
├── Preliminaries/                 generic cryptography — definitions only
│   ├── ...
├── Specification/                 what a zkVM is, and what it must prove
│   ├── Zkvm.lean                    abstract ZkVM + TraceValid
│   └── Cte.lean                     R*, CTE, and the keystone cte_iff_knowledgeSound
└── VMs/                           concrete VM machinery and instances, one subdirectory per VM
    ├── State.lean                   shared full/committed state shape
    ├── Memory.lean                  committed-to-full memory reconstruction
    ├── ISA.lean                     representative five-class execution predicate
    ├── Bus.lean                     reusable one-segment bus and extraction theorem
    └── TwoStep/                     non-recursive two-layer VM instance
        └── Bus.lean                 connects bus-backed segments to that VM
```

Dependencies point one way: **`Preliminaries/` → `Specification/` → `VMs/`.**

**`Preliminaries/`** holds everything that does not mention a virtual machine: argument systems and
what it means for one to be knowledge-sound, the memory and bus commitments with their binding
properties, and a couple of generic helpers. Definitions only — the proofs that consume them live
downstream.

**`Specification/`** states what we are trying to prove, once and abstractly. A zkVM is a state type
with a step relation, a step count, and a final verifier; it is *correct-trace extractable* when every
accepting proof can be turned into a valid execution reaching the claimed final state. Crucially this
layer knows nothing about memory commitments or instruction sets, which is what lets one definition
serve every VM.

**`VMs/`** holds the concrete machinery — VM states, the contract linking plain execution to
committed-memory execution, and the reconstruction of full memory from committed memory — plus one
subdirectory per concrete VM. Each such VM is an *instance* of the abstract zkVM above and proves
correct-trace extractability for itself, rather than restating the definition. So far there is one, a
deliberately minimal two-layer VM using a representative five-class ISA. The reusable bus module
models the separate step, Keccak, Poseidon, and range proofs for one segment without depending on
that VM. A small connection module then demonstrates whole-execution extraction
while retaining a distinct bus for each segment. Concrete opcode semantics and
the final recursive assembly are still to come.

Each `*Sanity.lean` file holds concrete models and countermodels witnessing that the definitions
beside it are satisfiable and the theorems consuming them non-vacuous — kept separate so the
definition files stay definitions-only.

The representative five-class ISA introduced by Issue 3 is documented in
[`docs/ISA.md`](docs/ISA.md).
The Issue 5 bus construction is described mathematically in
[`VanillaZkVM/math-companion.md`](VanillaZkVM/math-companion.md#4-segment-buses-and-one-complete-execution-issue-5).

## Idealization

The crypto layer is **perfect / probability-free**.
Currently, cryptographic building blocks are idealized as *perfect* to simplify everything.
For instance, collision-resistance is just defined as being injective; knowledge
soundness is `∃ extractor, ∀ accepting (x,p), witness valid`. There is no security parameter, no `negl`, no running time yet.
The paper itself flags a deeper caveat (`rem:idealized`): straight-line
extraction composed across recursion layers needs "relativized" SNARKs, which provably don't exist,
so even the paper's bounds validate reduction **structure**, not a concrete security level.

We are of course aware that this is far from being cryptographically accurate, and we may change this in the future.



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
