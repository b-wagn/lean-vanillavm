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
| Commitment completeness (instruction before `def:binding`) | `VanillaZkVM.VectorCommitment.Complete` | provisional | proved | — | — | _unreviewed_ |
| Position binding (`def:binding`) | `VanillaZkVM.VectorCommitment.PositionBinding` | provisional | proved | ✓ | ✓ | Dmitry 2026-07-29 |
| Update binding (`def:binding`) | `VanillaZkVM.VectorCommitment.UpdateBinding` | provisional | proved | — | — | _unreviewed_ |
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

## Memory extractability (Issue 1)

These declarations formalize the memory component only. `MemFreePredicate`
abstracts the PC/register transition and cannot itself connect a separate
`MemStep` value to registers. The dependencies and remaining work are tracked
in [`PLAN.md`](PLAN.md): Issue 3 now supplies that program/register connection,
while Issue 5 still adds the bus predicate.

For these rows, human review must separately check (a) that the read/write
opening and memory equations match the paper's memory slice, (b) that
`step_reconstruct_exact` constructs the next represented state without assuming
that the second committed state already represents a full state, and (c) that
no row is marked complete merely because
the later ISA/bus conjuncts live in another module. This distinguishes a
faithful memory component from the complete committed `φ̂_step`.

| Paper label | Lean declaration | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| full/committed memory invariant (`rem:mem-inheritance`) | `VanillaZkVM.CommitInv` | proved | — | — | _unreviewed_ |
| committed memory read/write (`eq:op-mem-comm-read`, `eq:op-mem-comm-write`) | `VanillaZkVM.CommittedMemory.read` / `CommittedMemory.write` | proved | — | — | _unreviewed_ |
| full-memory read/write (`eq:mem-op-read`, `eq:mem-op-write`) | `VanillaZkVM.FullMemory.read` / `FullMemory.write` | proved | — | — | _unreviewed_ |
| committed/full memory step (memory component of `φ̂_step`/`φ_step`) | `VanillaZkVM.CommittedMemory.step` / `FullMemory.step` / `VanillaZkVM.committedStep` | proved | — | — | _unreviewed_ |
| one-step memory lift (`prop:memory-extractability`) | `VanillaZkVM.step_mem_extract` | proved | — | — | _unreviewed_ |
| memory-inheritance step constructing the next full state (`rem:mem-inheritance`, `thm:main` Step 6) | `VanillaZkVM.step_reconstruct_exact` / `VanillaZkVM.step_reconstruct` / `VanillaZkVM.TwoStep.System.memoryBridge` | proved | — | — | _unreviewed_ |
| trace reconstruction invariant (`rem:mem-inheritance`) | `VanillaZkVM.trace_mem_extract` | proved | — | — | _unreviewed_ |
| — (joint satisfiability model, I6) | `VanillaZkVM.MemorySanity.exactVC_bindingAssumptions` | proved (n/a) | — | — | _unreviewed_ |
| — (punctured-condition countermodel, I6) | `VanillaZkVM.MemorySanity.appendBitVC_not_updateBinding` | proved (n/a) | — | — | _unreviewed_ |

## Representative ISA (Issue 3)

The paper's full opcode taxonomy is deliberately reduced to five representative
operation classes. `code` records only the class at each program counter, while
the PC/register predicates may still specify the exact fixed instruction there.
The class check and every memory equation are explicit. This issue therefore
specifies the five-way step structure, not an opcode decoder or an RV32IM
correctness proof. The `ISASanity` module gives private accepted and rejected
examples and checks that `stepPlain` can be used directly as `ZkVM.step`.
The two-step VM now performs that assignment publicly and requires each
committed `MemStep` to agree with the selected operation before reconstruction.
The read clause also requires unchanged memory, as stated by `eq:mem-op-read`
and the ch03 prose. The pinned `eq:phi-read-decomp` formula omits
that explicit condition; whitepaper proof-branch commit `aa33ed3` corrects it.
The affected fidelity review must account for this pending paper-pin update.

Human review must check more than elaboration: verify that the five classes are
an explicit representative simplification; that every `operation` contains the
fetch equation; that read/write address and value fields come from the stated
registers; that `committedOperation` rejects a mismatched `MemStep`; and that
`TwoStep.System.toZkVM.step` is exactly `stepPlain`. The reviewer should also
check that `indexOfWord` and `valueOfWord` merely convert machine words to the
memory's address and value types; the actual instruction requirements must
remain in `memFreePred`. The complete checklist is in
[`ISA.md`](ISA.md#human-review-checklist).

**Reviewer action:** after checking the PR head, replace the em dashes and
`_unreviewed_` entries below with the fidelity/completeness decision, reviewer
name, and date **in a separate review commit**. Do not edit these cells in the
implementation commit: the separate commit records human sign-off on a stable
code-and-guide version.

| Paper label | Lean declaration | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| operation taxonomy (ch03, deliberately simplified) | `VanillaZkVM.ISA.OperationClass` | proved | — | — | _unreviewed_ |
| fixed `code` class, selected per-operation `φ'_op`, and register-word interpretation (`eq:phiop`) | `VanillaZkVM.ISA.System` / `VanillaZkVM.ISA.System.selectedMemFreePred` | proved | — | — | _unreviewed_ |
| `φ_op`, including fetch and memory equations (`eq:phiop`, `eq:phi-read-decomp`, `eq:phi-write-decomp`) | `VanillaZkVM.ISA.System.operation` | proved | — | — | _unreviewed_ |
| disjunctive `φ_step` (`eq:step`) | `VanillaZkVM.ISA.System.stepPlain` | proved | — | — | _unreviewed_ |
| program-selected committed operation, without bus (`eq:step-bus2`) | `VanillaZkVM.ISA.System.committedOperation` / `VanillaZkVM.ISA.System.committedStep` | proved | — | — | _unreviewed_ |
| instruction selection by `code[pc]` (`eq:op`, `eq:phiop`) | `VanillaZkVM.ISA.System.stepPlain_iff_operation_at_pc` | proved | — | — | _unreviewed_ |
| non-write operations preserve memory (ch01/ch03) | `VanillaZkVM.ISA.System.operation_preserves_memory_unless_write` | proved | — | — | _unreviewed_ |
| committed/full operation correspondence (`prop:memory-extractability`, `thm:main` Step 6) | `VanillaZkVM.ISA.System.committedOperation_stepPlain` | proved | — | — | _unreviewed_ |

## Two-step toy (intermediate)

| Paper label | Lean declaration | Status | Fidelity | Complete | Reviewer |
|---|---|---|---|---|---|
| segment/final toy relations | `TwoStep.System.RSeg` / `RFinal` | proved | — | — | _unreviewed_ |
| representative `φ_step` used as the concrete toy VM step (`eq:step`) | `VanillaZkVM.TwoStep.System.toZkVM` | proved | — | — | _unreviewed_ |
| — (two-layer committed-chain extraction, intermediate) | `VanillaZkVM.TwoStep.System.committedTrace_extract` | proved (n/a) | n/a | n/a | _unreviewed_ |
| toy CTE over full memory (`def:cte`, `prop:memory-extractability`) | `VanillaZkVM.TwoStep.System.cte` | proved | — | — | _unreviewed_ |

## Planned (owned by issues — see PLAN.md)

| Paper label | Lean declaration (planned name) | Owner issue |
|---|---|---|
| `R_{0,step}` and the inner chip relations | _name pending Issue-5 definition review_ | Issue 5 |
| `R_1` segment relation and extraction (`lem:segment`) | _name pending Issue-5 definition review_ | Issue 5 |
| bus unification under CR of `Com_bus` | _name pending Issue-5 definition review_ | Issue 5 |
| `R_2` convert (`lem:convert`) | `MultiStep.RConvert` | Issue 4 |
| `R_3` combine + tree unrolling (`lem:combine`) | `MultiStep.RCombine` / `combine_tree` | Issue 4 |
| `R_4` embed (`lem:embed`) | `MultiStep.REmbed` | Issue 4 |
| bus-deferred step `φ̂_step` (`eq:step-expanded`) + per-execution bus lift (`thm:main` 4–5) | `Bus.*` (redone) + `concatTrace` glue | Issue 5 |
| main theorem (`thm:main`) | `VanillaVM.cte_main` | Issue 7 |
| advantage / negligibility vocabulary | _name pending Issue-10 definition review_ | Issue 10 |
| per-layer reduction bounds + `thm:main` weighted sum | _name pending Issue-6 definition review_ | Issue 6 |
