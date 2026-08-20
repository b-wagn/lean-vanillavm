# Session 2026-08-18 — Issue 3 rebase and fixed-program clarification

## Bootstrap

- **Issue:** `docs/PLAN.md` → Issue 3 (representative ISA operations).
- **Branch:** `yl-issue-3`, rebased from retired `main-temp` onto `origin/main`
  at `c24851a`.
- **Read at start:** `README.md`, `docs/INVARIANTS.md`,
  `docs/CONVENTIONS.md`, the Issue 3 section of `docs/PLAN.md`,
  `docs/CORRESPONDENCE.md`, `docs/STEP_INTERFACES.md`, and the pinned ch01
  execution-model source.
- **Build after rebase:** `lake build` green (8,597 jobs).

## What changed

- Moved the Issue 3 modules into the restructured `VanillaZkVM/VMs/`
  directory and preserved `main`'s new module boundaries.
- Added `ISA.System.stepPlain_iff_operation_at_pc`, which proves that the
  five-way `stepPlain` disjunction is exactly the operation class selected by
  `code S₁.pc`.
- Initially documented `TwoStep.System.toZkVM` as the Issue 1 memory-only toy
  and deferred its ISA connection. Benedikt and Dmitry subsequently requested
  that connection in Issue 3; the superseding implementation and audit are
  recorded in
  [`2026-08-19-issue-3-review-followup.md`](2026-08-19-issue-3-review-followup.md).
- Updated the math companion, human review guide, and correspondence matrix.

## Scope and public surface

- No additional VM instance was introduced. The only new public declaration in
  this original follow-up was
  `ISA.System.stepPlain_iff_operation_at_pc`.
- The later integration added the committed/plain bridge declarations listed
  in the 2026-08-19 ledger entry above.

## Validation

- `lake build`: green (8,597 jobs).
- Full CI audit: green; all 39 audited correspondence declarations elaborate,
  and 563 declarations pass the repository-wide hygiene scan.
- `stepPlain_iff_operation_at_pc` depends only on the permitted `propext`
  axiom.
- No `sorry`, `admit`, `native_decide`, or new axiom was added.

These figures describe the original 2026-08-18 revision. The current PR-head
audit is recorded in the 2026-08-19 follow-up ledger.

## Handoff

The original two-sentence handoff was too terse. A reviewer must check the
five-class simplification, instruction selection by `code[pc]`, every memory
equation, agreement between each committed `MemStep` and the designated
registers, direct use of `stepPlain` as `TwoStep.System.toZkVM.step`, and the
accepted/rejected sanity examples. The exact six-part checklist is in
[`docs/ISA.md`](../ISA.md#human-review-checklist), and the current scope/axiom
ledger is in
[`2026-08-19-issue-3-review-followup.md`](2026-08-19-issue-3-review-followup.md).
The PR description must copy that checklist or link directly to it. Human
fidelity/completeness sign-off must then be recorded in a separate commit, as
instructed by `docs/CORRESPONDENCE.md`.
