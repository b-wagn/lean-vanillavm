# CORRESPONDENCE — Lean ↔ paper matrix

One row per formalized paper item. This is the surface a reviewer reads **with the paper open next
to it** (Hicks: the finality-repo handover pattern). It is also the audit anchor: a reviewer's
sign-off is a per-row act ("this Lean declaration faithfully and completely formalizes this paper
statement"). Adapted from `finality/CORRESPONDENCE.md`.

**Status vocabulary:** `stated` (statement written, proof may be `sorry`) · `proved` (proof
complete, axiom-clean) · `pending(N)` (blocked on N other rows) · `n/a` (Lean-only scaffolding, no
paper counterpart) · `planned` (not yet in code; owned by an issue).

**Reviewer columns:** `Fidelity` = does the Lean statement mean the paper statement? ·
`Complete` = does it cover the *whole* paper statement, not a faithful fragment? (finality learned
"faithful but partial" is a distinct failure mode.) · `Reviewer` = collaborator who signed off +
date.

**Rule (I1, CI-checked):** every declaration formalizing a paper notion has a docstring citing the
paper label AND a row here; the named Lean declaration must actually elaborate (`#check`).

**Normative paper revision:** `a0f5e0b63395a2fddce3f949c4de1df9264a174b` on the whitepaper's
`proof` branch; see [`PAPER_REVISION.md`](PAPER_REVISION.md). In particular, `code` and `T` are
fixed system parameters in `def:cte`.

This matrix remains **paper-item keyed**. Frozen Lean infrastructure that is not itself the
selected formalization of a complete paper item (`Relation`, `Extractor`, the abstract `ZkVM`
packaging, `TraceValid`, and the `StepInterface` coordination scaffold) belongs to I4 but does not
receive an artificial row here.

## Core

**Frozen kernel (I4)** — the stable heart. **Provisional** — the commitment layer, expected to
change (see notes below the table).

| Paper label | Lean declaration | Tier | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|---|
| Argument system Π=(Prove,Verify) | `VanillaZkVM.ArgumentSystem` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Knowledge soundness (`def:extractable`) | `VanillaZkVM.KnowledgeSound` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| — (consistency floor for KS) | `VanillaZkVM.knowledgeSound_trivialAS` | scaffolding | proved (n/a) | n/a | n/a | Dmitry 2026-07-29 |
| VM state S=(pc,regs,mem) (ch01) | `VanillaZkVM.VMStateWith` / `VMState` | support | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Committed state Ŝ (ch02) | `VanillaZkVM.CommittedVMState` | support | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Correct-execution relation R* (`eq:relation-star`) | `VanillaZkVM.ZkVM.Rstar` | frozen | proved | ✓ | ✗ (see ‡) | Dmitry 2026-07-29 |
| Correct-trace extractability (`def:cte`) | `VanillaZkVM.ZkVM.CTE` | frozen | proved | ✓ | ✗ (see †) | Dmitry 2026-07-29 |
| CTE ⇔ KS (`rem:cte-ks`) | `VanillaZkVM.ZkVM.cte_iff_knowledgeSound` | frozen | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Merkle memory commitment `Com_mem` (ch02) | `VanillaZkVM.VectorCommitment` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Commitment completeness (instruction before `def:binding`) | `VanillaZkVM.Complete` | provisional | proved | — | — | _unreviewed_ |
| Position binding (`def:binding`) | `VanillaZkVM.PositionBinding` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Update binding (`def:binding`) | `VanillaZkVM.UpdateBinding` | provisional | proved | — | — | _unreviewed_ |
| Bus commitment `Com_bus` (`def:bus-cr`) | `VanillaZkVM.HashCommitment` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Collision resistance (`Adv^cr`) | `VanillaZkVM.CollisionResistant` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |

> **‡ `Rstar` is an abstract relation skeleton, not yet the whole concrete `R*`.** Its witness is a
> trace satisfying the selected `ZkVM.step` and boundary projections, but the current abstract
> declaration neither requires statements to contain full-memory boundary states nor constrains
> the verifier to commit those states as specified immediately after `eq:relation-star`. Issue 7
> supplies that concrete boundary/verifier package in the full Vanilla VM instance. Fidelity to the
> trace-validity component is signed; completeness is not.

> **† `CTE` completeness is deliberately left unsigned.** `ZkVM.CTE` is *faithful* to
> `def:cte` (fidelity ✓), but it is not signed off as covering the paper definition in full: the
> paper's `def:cte` is **too verbose** and should probably itself be **refactored**. Until that
> refactor happens, claiming completeness against the current paper text would be signing off on a
> statement we expect to restate. Re-open this row once `def:cte` is tightened.

> **Note (I4).** The paper states position binding and update binding as
> **independent** properties. Update binding supplies the commitment-realizability
> guarantee needed after a write; the punctured non-equivocation condition did
> not. The entire `VectorCommitment` binding layer and `CollisionResistant` remain
> *provisional* and may gain keyed/algorithmic variants.

## Leaf / segment / bus (ch04) — ⚠ PROTOTYPE, NOT GROUND TRUTH

> `main-temp`'s `Bus.lean` is **Yavor's playground prototype**, not authoritative. These rows are
> **not** audited checkpoints; the layer is **redone properly in Issue 5** (over the frozen kernel
> and the Issue-3 ISA). Treat the current declarations as reference only.

| Paper label | Lean declaration (prototype) | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| `R_{0,step}` (inner-step) | `Bus.System.RInnerStep` | prototype | — | — | Issue 5 |
| `R_{0,keccak/poseidon/range}` (chips) | `Bus.System.RInner{Keccak,Poseidon,Range}` | prototype | — | — | Issue 5 |
| `R_1` (segment) | `Bus.System.RSegment` | prototype | — | — | Issue 5 |
| segment extraction (`lem:segment`) | `Bus.System.segment_extract` | prototype | — | — | Issue 5 |
| bus unification / extract-or-collision | _Issue 2 (shape) → Issue 5 (wired)_ | planned | — | — | — |

## Memory extractability (Issue 1)

These declarations formalize the memory component only. `MemFreePredicate`
abstracts the PC/register transition and does not yet connect descriptor fields
to registers; the concrete ISA, bus, and their conjunction with this component
remain Issues 3 and 5. Human review must therefore judge fidelity to the memory
slice separately from completeness of the eventual `φ_step`.

| Paper label | Lean declaration | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| full/committed memory invariant (`rem:mem-inheritance`) | `VanillaZkVM.CommitInv` | proved | — | — | _unreviewed_ |
| committed memory read/write (`eq:op-mem-comm-read`, `eq:op-mem-comm-write`) | `VanillaZkVM.readC` / `writeC` | proved | — | — | _unreviewed_ |
| full-memory read/write (`eq:mem-op-read`, `eq:mem-op-write`) | `VanillaZkVM.readF` / `writeF` | proved | — | — | _unreviewed_ |
| classified committed/full memory step (memory component of `φ̂_step`/`φ_step`) | `VanillaZkVM.stepC` / `stepF` / `committedStep` | proved | — | — | _unreviewed_ |
| one-step memory lift (`prop:memory-extractability`) | `VanillaZkVM.step_mem_extract` | proved | — | — | _unreviewed_ |
| constructive memory-inheritance step (`rem:mem-inheritance`, `thm:main` Step 6) | `VanillaZkVM.step_reconstruct` / `VanillaZkVM.TwoStep.System.memoryBridge` | proved | — | — | _unreviewed_ |
| trace reconstruction invariant (`rem:mem-inheritance`) | `VanillaZkVM.trace_mem_extract` | proved | — | — | _unreviewed_ |
| — (joint satisfiability model, I6) | `VanillaZkVM.MemorySanity.exactVC_bindingAssumptions` | proved (n/a) | — | — | _unreviewed_ |
| — (punctured-condition countermodel, I6) | `VanillaZkVM.MemorySanity.appendBitVC_not_updateBinding` | proved (n/a) | — | — | _unreviewed_ |

## Two-step toy (intermediate)

| Paper label | Lean declaration | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| segment/final toy relations | `TwoStep.System.RSeg` / `RFinal` | proved | — | — | _unreviewed_ |
| toy CTE (committed memory) | `VanillaZkVM.TwoStep.System.cte` | proved | — | — | _unreviewed_ |
| toy CTE over full memory (`def:cte`, `prop:memory-extractability`) | `VanillaZkVM.TwoStep.System.cte_full` | proved | — | — | _unreviewed_ |

## Planned (owned by issues — see PLAN.md)

| Paper label | Lean declaration (planned name) | Owner issue |
|---|---|---|
| ISA op set `{read, write, arith, hash, bin}` + `φ'_op` split (ch03, simplified) | `ISA.*` | Issue 3 |
| `R_2` convert (`lem:convert`) | `MultiStep.RConvert` | Issue 4 |
| `R_3` combine + tree unrolling (`lem:combine`) | `MultiStep.RCombine` / `combine_tree` | Issue 4 |
| `R_4` embed (`lem:embed`) | `MultiStep.REmbed` | Issue 4 |
| bus-deferred step `φ̂_step` (`eq:step-expanded`) + per-execution bus lift (`thm:main` 4–5) | `Bus.*` (redone) + `concatTrace` glue | Issue 5 |
| main theorem (`thm:main`) | `VanillaVM.cte_main` | Issue 7 |
| advantage / reduction vocabulary | `Reduction.*` | Issue 2/6 |
