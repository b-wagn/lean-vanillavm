# Vanilla zkVM — Lean formalization

A Lean 4 / Mathlib formalization of the **Vanilla zkVM** and its main security result, ported from
the Ethereum Foundation zkVM whitepaper example (`zkvm-whitepaper/sampleVM/`, chapters ch01–ch05).
The goal is to formalize **correct-trace extractability (CTE)** — that an accepting final proof lets
an extractor recover a full, valid execution trace — for a recursive zkVM with committed memory and
a bus, reducing security to explicit cryptographic hardness assumptions.

> **Status: WIP.** The current core is small, clean, and axiom-clean, but idealized (see
> [Idealization](#idealization)). The path from here to the full theorem is [`docs/PLAN.md`](docs/PLAN.md).

---

## For Benedikt (and anyone joining) — start here

Everything you need is in `docs/`, in this reading order:

1. [`docs/INVARIANTS.md`](docs/INVARIANTS.md) — the project constitution (11 rules; the "why" behind
   every decision). **Read first.**
2. [`docs/PLAN.md`](docs/PLAN.md) — the 10 development issues, dependency graph, who owns what, and
   the per-issue review requirements.
3. [`docs/CONVENTIONS.md`](docs/CONVENTIONS.md) — how we write Lean, use agents, and review.
4. [`docs/CORRESPONDENCE.md`](docs/CORRESPONDENCE.md) — the Lean ↔ paper matrix (the audit surface).
5. Background digests (generated, for reference): [`docs/hicks-digest.md`](docs/hicks-digest.md)
   (Alex Hicks's advice), [`docs/paper-digest.md`](docs/paper-digest.md) (the whole proof structure),
   [`docs/branch-analysis.md`](docs/branch-analysis.md) (what's in every git branch),
   [`docs/vcvio-analysis.md`](docs/vcvio-analysis.md), [`docs/finality-analysis.md`](docs/finality-analysis.md)
   (conventions/skills inherited from our colleagues' libraries).

The single most important idea, from the Hicks meeting: **the definitions are 80% of the value.**
The *kernel* — `KnowledgeSound`, `CTE`, the abstract `ZkVM`, `cte_iff_knowledgeSound` — is frozen and
heavily reviewed; everything else just has to type-check and be non-vacuous. The commitment binding
layer is deliberately **not** frozen (it is still changing — `PuncturedBinding` is being retired in
favour of `UpdateBinding`); see `docs/INVARIANTS.md` I4.

**Roles.** Implementers: **Yavor, Dmitry, Jessica** (assigned to the code they already wrote —
memory, recursion/cost, and reductions respectively). **Benedikt reviews only** for now (on
vacation). **George reviews now and is likely to join as an implementer** (natural fit: the
recursion topology in Issue 4 and the reduction/capstone Issues 6–7). No one reviews their own
issue. See `docs/PLAN.md`.

---

## Current architecture (what exists on `main-temp`)

Four files, ~750 lines, `lake build`-green, axiom set `{propext, Quot.sound}`:

| File | Contents |
|---|---|
| `VanillaZkVM/Crypto.lean` | **Frozen kernel** `Relation`, `ArgumentSystem`, `Extractor`, `KnowledgeSound` (+ `trivialAS` consistency floor); **provisional** commitment layer `VectorCommitment` with `PositionBinding`/`PuncturedBinding` (the latter insufficient — being replaced by `UpdateBinding`), `HashCommitment` with `CollisionResistant`. All *perfect* (probability-free). |
| `VanillaZkVM/Zkvm.lean` | **Frozen kernel.** Abstract `ZkVM`, `TraceValid`, `R* = Rstar`, `CTE`, and the keystone `cte_iff_knowledgeSound`. Plus the reusable `concatTrace` / `chain_flatten` glue lemma. |
| `VanillaZkVM/Twostep.lean` | A minimal 2-layer VM (`RSeg → RFinal`) instantiating `ZkVM`, with `Assumptions{ksSeg,ksFinal}` and theorem `cte`. Toy — no memory extraction, no bus. |
| `VanillaZkVM/Bus.lean` | ⚠ **Yavor's playground prototype — NOT ground truth.** A first cut of the leaf/segment layer (four inner circuits, `RSegment`, `segment_extract`). It is *reference only*; the real segment/bus layer is (re)built in Issue 5. |

**How it maps to the paper.** `CTE ⇔ KnowledgeSound` is the paper's `rem:cte-ks`. The abstract
`ZkVM` + `R*` are ch03/ch05. (`Bus.lean`'s `segment_extract` gestures at `lem:segment` but is a
prototype, not an audited result.) See `docs/CORRESPONDENCE.md` for the full row-by-row map.

## Checkpoints (roadmap at a glance)

Detailed in [`docs/PLAN.md`](docs/PLAN.md). Critical path: **0 → {1,4} → 6 → 7** (the bus, Issue 5,
is intentionally late — recursion is built over an abstract leaf and doesn't need it).

- [x] **C0. Kernel defined.** Abstract `ZkVM`, `CTE`, `cte_iff_knowledgeSound`, perfect crypto. *(done)*
- [x] **C1. Toy VM CTE.** Two-step VM proven CTE from KS of both layers. *(done)*
- [~] **C2. Segment/bus prototype.** `Bus.lean` exists (Yavor's playground) — *prototype, to be redone in Issue 5, not an audited checkpoint.*
- [ ] **C3. Kernel frozen + scaffolding** — Issue 0.
- [ ] **C4. Committed memory** → `TwoStepWithMemory`, CTE from memory-commitment binding (`UpdateBinding` replaces `PuncturedBinding`) — Issue 1.
- [ ] **C5. Reduction vocabulary** (extract-or-break) — Issue 2.
- [ ] **C6. ISA op set** `{read, write, arith, hash, bin}` — Issue 3.
- [ ] **C7. Real recursion** → `MultiStepVM` (convert/combine/embed + tree unrolling) — Issue 4.
- [ ] **C8. Bus per segment, wired into a VM** (redone properly) — Issue 5.
- [ ] **C9. Explicit per-layer reductions** (the `thm:main` weighted sum) — Issue 6.
- [ ] **C10. Full Vanilla VM + main theorem** (`cte_main` ≈ `thm:main`) — Issue 7.
- [ ] **Parallel:** security-model & runtime study — Issue 8; audit + independent re-derivation — Issue 9.

## Idealization

Following the Hicks meeting (I8), the crypto layer is **perfect / probability-free**: knowledge
soundness is `∃ extractor, ∀ accepting (x,p), witness valid`; binding is exact; collision-resistance
is injectivity. There is no security parameter, no `negl`, no running time yet. This is deliberate —
it keeps the development self-contained and lets us focus on the load-bearing *definitions* and
*reduction structure*. The paper itself flags a deeper caveat (`rem:idealized`): straight-line
extraction composed across recursion layers needs "relativized" SNARKs, which provably don't exist,
so even the paper's bounds validate reduction **structure**, not a concrete security level. Lifting
to concrete/asymptotic security (and importing VCVio) is scoped as the *optional* Issue 8, not a
prerequisite.

## Build

```bash
lake build
```

Requires the toolchain pinned in `lean-toolchain` and Mathlib `v4.32.0-rc1` (see `lakefile.toml`).
Every PR must keep `lake build` green and satisfy `#print axioms` ⊆ `{propext, Classical.choice,
Quot.sound}` (I7).

## Contributing

Read `docs/INVARIANTS.md` and `docs/CONVENTIONS.md`, pick an issue from `docs/PLAN.md`, branch from
`main-temp`, and open a PR back into `main-temp`. Each issue names a required human reviewer whose
core judgement — *is this the right definition?* — is explicitly **not** delegatable to an agent.
