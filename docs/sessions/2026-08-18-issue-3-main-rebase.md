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
- Clarified that `TwoStep.System.toZkVM` remains the Issue 1 memory-only toy:
  its existential `MemStep` is not the final fixed-program semantics. Issue 5
  will connect extracted memory/bus evidence to the selected operation, and
  Issue 7 will assemble the public VM using `ISA.System.stepPlain`.
- Updated the math companion, human review guide, and correspondence matrix.

## Scope and public surface

- No additional VM instance was introduced. The only new public declaration
  in this follow-up is the bridge theorem
  `ISA.System.stepPlain_iff_operation_at_pc`; it exposes no competing step
  relation.
- The existing private instance in `VMs/ISASanity.lean` continues to check that
  `stepPlain` can be assigned directly to `ZkVM.step`.

## Validation

- `lake build`: green (8,597 jobs).
- Full CI audit: green; all 39 audited correspondence declarations elaborate,
  and 563 declarations pass the repository-wide hygiene scan.
- `stepPlain_iff_operation_at_pc` depends only on the permitted `propext`
  axiom.
- No `sorry`, `admit`, `native_decide`, or new axiom was added.

## Handoff

- George should review both the five-class simplification and the equivalence
  between `stepPlain` and the operation selected by `code S₁.pc`.
- Integrating `MemStep` and bus evidence with that selected operation remains
  Issue 5; constructing the public full Vanilla VM remains Issue 7.
