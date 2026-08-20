# Session 2026-08-19 — Issue 3 review follow-up

## Bootstrap

- **Issue:** [`PLAN.md`](../PLAN.md), Issue 3 (representative ISA operations).
- **Branch:** `yl-issue-3`, rebased onto `origin/main` at `47ed95c` before the
  follow-up edits.
- **Human feedback:** PR #19 inline comments from Dmitry, plus Benedikt's request
  to make the two-step VM use the program-selected operation instead of an
  unconstrained existential `MemStep`.
- **Read at start:** `README.md`, `INVARIANTS.md`, `CONVENTIONS.md`, Issue 3 in
  `PLAN.md`, `CORRESPONDENCE.md`, `STEP_INTERFACES.md`, the relevant state,
  memory, ISA, and two-step modules, and the pinned ch01 execution semantics.
- **Baseline build after rebase:** `lake build` green (8,597 jobs).

## What changed

- Parameterized `ISA.System` over memory index/value types and made the
  interpretation of register words explicit. The paper's `VMState`, `Addr`,
  and `Byte` remain its ordinary Chapter 1 state and scalar names; the generic
  parameters let the same ISA act directly on `FullVMState VC` without
  defining another structure with different fields.
- Added `ISA.System.committedOperation`, which requires each explicit
  `MemStep` to agree with `code[pc]` and with the designated address/value
  registers. Added `committedStep` to state that some `MemStep` passes those
  checks when the actual value need not be exposed.
- Added `step_reconstruct_exact`, retaining the supplied `MemStep` through
  one-step memory reconstruction, and
  `ISA.System.committedOperation_stepPlain`, which turns that reconstructed
  transition into the VM's plain step.
- Replaced `TwoStep.System.memFreePred` with `TwoStep.System.isa`; `RSeg` and
  `CommittedTraceValid` now use the ISA-aware committed relation, and
  `TwoStep.System.toZkVM.step` is exactly `ISA.System.stepPlain`.
- Extended the private two-step model with an accepted arithmetic `.other`
  witness, rejection of a read witness for the same program counter, an
  accepted plain step, and the existing full CTE check.
- Expanded the review guide and correspondence matrix with a precise human
  checklist, an instruction to record sign-off in a separate commit, links to
  `PLAN.md`, and a warning that review applies only to the code at the reviewed
  Git commit.

## Feedback resolution

- **State names:** `State.lean` and the review guide now explain why `Addr`,
  `Byte`, and `VMState` remain. They name the paper's ordinary `Addr → Byte`
  state, while both that state and `FullVMState VC` use the same `VMStateWith`
  structure containing the `pc`, `regs`, and `mem` fields.
- **Two-step execution:** `TwoStep.System.toZkVM.step` is now `stepPlain`.
  `stepPlain_iff_operation_at_pc` shows that this executes exactly
  `operation (code S₁.pc)`, so an arbitrary `MemStep` no longer chooses the
  plain VM operation.
- **Why `MemStep` remains:** committed reads and writes still need an opening
  proof for memory reconstruction. `RSeg` therefore stores `MemStep` values,
  but `committedOperation` checks them against `code[pc]` and the designated
  registers before they can be accepted.
- **Review handoff:** the older session note now states the concrete review
  questions and points to the full checklist in `ISA.md`.
- **Stable references and sign-off:** `CORRESPONDENCE.md` links to `PLAN.md`,
  expands the human review requirements, and directly asks the reviewer to
  record fidelity, completeness, name, and date in a separate commit.
- **Versioned guide:** `ISA.md` warns that its prose applies only to the code at
  the same Git commit. When this revision is pushed, the PR description must be
  refreshed from that guide before review threads are marked resolved.

## Scope and public surface

The original Issue 3 surface remains `ISA.OperationClass`, `ISA.System`,
`ISA.System.operation`, and `ISA.System.stepPlain`, together with its two main
theorems. This follow-up adds five public declarations needed to connect that
surface to the existing two-step VM:

- `selectedMemFreePred` makes the committed and full checks select the same
  PC/register requirements;
- `committedOperation` is the explicit relation used by public `RSeg`;
- `committedStep` supplies the two-state relation required by
  `StepInterface` and `CommittedTraceValid`;
- `step_reconstruct_exact` preserves the particular `MemStep` needed by the
  ISA check across memory reconstruction; and
- `committedOperation_stepPlain` proves the final connection to `stepPlain`.

Each declaration crosses a module boundary and is used by the public two-step
VM or its frozen memory interface, so making it private would only force the
same statement to be duplicated. No second plain step predicate or additional
`ZkVM` instance was introduced; `stepPlain` is the sole `ZkVM.step` for this
VM. The direct team request to integrate the two-step VM is the reason this
follow-up is larger than Issue 3's original approximate surface estimate.

The branch still does not model a concrete opcode decoder, prove individual
RV32IM operations, add bus/chip evidence, or construct the recursive Vanilla
VM. Those remain assigned by `PLAN.md`.

## Validation

- `lake build`: green (8,597 jobs).
- Full CI audit: green; all 45 audited correspondence declarations elaborate,
  and 586 declarations pass the repository-wide hygiene scan.
- The three Issue 3 headline theorems use only permitted axioms:
  `stepPlain_iff_operation_at_pc` and
  `operation_preserves_memory_unless_write` use `propext`;
  `committedOperation_stepPlain` uses `propext` and `Quot.sound`.
- `step_reconstruct_exact`, the memory helper exposed for the ISA bridge, uses
  only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `native_decide`, direct `sorryAx`, or new `axiom` was
  added.

## Handoff

The definition-level review checklist is in
[`ISA.md`](../ISA.md#human-review-checklist). The reviewer should confirm the
five-class simplification, fetch and memory equations, committed-witness
agreement, reconstruction using the same `MemStep`, and the direct assignment
of `stepPlain` to `TwoStep.System.toZkVM.step`. Human sign-off belongs in a
separate commit updating the Issue 3 cells in `CORRESPONDENCE.md`.
