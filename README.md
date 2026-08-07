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

## For Benedikt (and anyone joining) — start here

Everything you need is in `docs/`, in this reading order:

1. [`docs/INVARIANTS.md`](docs/INVARIANTS.md) — the project constitution (11 rules; the "why" behind
   every decision). **Read first.**
2. [`docs/PLAN.md`](docs/PLAN.md) — the 10 development issues, dependency graph, who owns what, and
   the per-issue review requirements.
3. [`docs/CONVENTIONS.md`](docs/CONVENTIONS.md) — how we write Lean, use agents, and review.
4. [`docs/CORRESPONDENCE.md`](docs/CORRESPONDENCE.md) — the Lean ↔ paper matrix (the audit surface).
5. [`docs/PAPER_REVISION.md`](docs/PAPER_REVISION.md) and
   [`docs/STEP_INTERFACES.md`](docs/STEP_INTERFACES.md) — the exact paper pin and the
   plain/committed/bus step contract.
6. [`docs/MEMORY_RECONSTRUCTION.md`](docs/MEMORY_RECONSTRUCTION.md) — the human-readable
   review guide for the Issue 1 committed-memory reconstruction layer.
7. Background digests (generated, for reference): [`docs/paper-digest.md`](docs/paper-digest.md)
   (the whole proof structure),
   [`docs/branch-analysis.md`](docs/branch-analysis.md) (what's in every git branch),
   [`docs/vcvio-analysis.md`](docs/vcvio-analysis.md), [`docs/finality-analysis.md`](docs/finality-analysis.md)
   (conventions/skills inherited from our colleagues' libraries).

The single most important idea, from the Hicks meeting: **the definitions are 80% of the value.**
The *kernel* — `KnowledgeSound`, `CTE`, the abstract `ZkVM`, `cte_iff_knowledgeSound` — is small and
explicitly frozen under I4. Dmitry signed the current paper-facing rows on 2026-07-29; any later
signature change follows I4's re-review process. The commitment binding layer is deliberately
**not** frozen. Issue 1 replaces the insufficient `PuncturedBinding` predicate with the paper's
independent `PositionBinding` and `UpdateBinding` properties.

**Roles.** Implementers: **Yavor, Dmitry, Jessica** (assigned to the code they already wrote —
memory, recursion/cost, and reductions respectively). **Benedikt reviews only** for now (on
vacation). **George reviews now and is likely to join as an implementer** (natural fit: the
recursion topology in Issue 4 and the reduction/capstone Issues 6–7). No one reviews their own
issue. See `docs/PLAN.md`.

---

## Current architecture

The umbrella module imports the following focused modules. The branch is `lake build`-green and CI
permits only `{propext, Classical.choice, Quot.sound}`:

| File | Contents |
|---|---|
| `VanillaZkVM/Crypto.lean` | Definitions only: frozen `Relation`, `ArgumentSystem`, `Extractor`, `KnowledgeSound`; provisional `Complete`, `PositionBinding`, and `UpdateBinding` commitment notions. |
| `VanillaZkVM/CryptoSanity.lean` | I6 consistency floor for `KnowledgeSound` (`trivialAS`). |
| `VanillaZkVM/Zkvm.lean` | Frozen abstract `ZkVM`, `TraceValid`, `Rstar`, `CTE`, and `cte_iff_knowledgeSound`. |
| `VanillaZkVM/Step.lean` | Frozen committed-step interface and the memory/bus bridge propositions; `ZkVM.step` remains the plain predicate. |
| `VanillaZkVM/ZkvmSanity.lean` | Private accepting one-step model witnessing CTE and bridge satisfiability. |
| `VanillaZkVM/Trace.lean` | Reusable `concatTrace` / `chain_flatten` glue. |
| `VanillaZkVM/Memory.lean` | The memory-only committed/full step interface, update-binding reconstruction invariant, one-step bridge, and whole-trace fold. |
| `VanillaZkVM/MemorySanity.lean` | A jointly satisfiable binding model and the append-bit countermodel showing why update binding is needed. |
| `VanillaZkVM/Twostep.lean` | A minimal two-layer VM (`RSeg → RFinal`) with committed CTE `cte_committedMemory` and full-memory CTE `cte_fullMemory`. It still omits the concrete ISA, bus, and recursion tower. |
| `VanillaZkVM/TwostepSanity.lean` | A private accepting model witnessing that all `cte_fullMemory` hypotheses are jointly satisfiable. |
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
- [~] **C3. Kernel frozen + scaffolding** — implementation complete; human ratification remains — Issue 0.
- [~] **C4. Committed memory** → `TwoStepWithMemory`, CTE from position/update binding — implementation complete; human definition review remains — Issue 1.
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
