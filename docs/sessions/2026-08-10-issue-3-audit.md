# Session 2026-08-10 — final Issue 3 audit

## Bootstrap
- **Issue:** `PLAN.md` → Issue 3 (representative ISA operation classes).
- **Branch:** `yl-issue-3`, based on `main-temp` at `b40d8a4`.
- **Read at start:** `README.md`, `INVARIANTS.md`, `CONVENTIONS.md`, the Issue 3
  section of `PLAN.md`, `CORRESPONDENCE.md`, `STEP_INTERFACES.md`, the pinned
  ch01/ch03 paper text, and GitHub Issue #9.
- **Build at start:** the unchanged draft inherited the green 8,593-job build
  recorded in `2026-08-07-issue-3-isa.md`.

## OpenVM comparison
- Reviewed [`openvm-org/openvm-fv`](https://github.com/openvm-org/openvm-fv/tree/7523c23a3148100a0f201b33385c0f8e01b2c858)
  at commit `7523c23`. Its scope is much more concrete: it decodes exact
  instructions, gives pure reference behavior for individual RV32IM opcodes,
  and proves implementation behavior equivalent to that reference behavior.
- The exact-opcode and AIR layers were not copied because Issue 3 deliberately
  keeps instruction semantics abstract and models only five classes. Two useful
  structural lessons were retained: dispatch is exhaustive rather than using a
  catch-all branch, and the code distinguishes its class-level step structure
  from a future exact-opcode correctness proof.

## What changed
- Renamed `ISA.Operation` to `ISA.OperationClass` so readers do not mistake the
  five routing cases for decoded instructions.
- Clarified that `System.code` records the operation class at each program
  counter, while `memFreePred` supplies the remaining PC/register requirements
  and may distinguish exact instructions by their program counter.
- Made all five branches of `System.operation` explicit and simplified comments
  throughout the Lean files, math companion, README, and review matrix.
- Added `docs/ISA.md`, Yavor's human-level guide to the three Lean files and
  their principal definitions, examples, and scope boundary.
- Recorded a paper-revision discrepancy: the pinned `eq:phi-read-decomp` omits
  unchanged memory even though the paper's read semantics require it;
  proof-branch commit `aa33ed3` adds the missing condition used by Lean.
- New public surface (I5): unchanged in size. The four definitions are
  `ISA.OperationClass`, `ISA.System`, `ISA.System.operation`, and
  `ISA.System.stepPlain`; the required result is
  `ISA.System.operation_preserves_memory_unless_write`.

## Axiom / `sorry` ledger diff
- `#print axioms ISA.System.operation_preserves_memory_unless_write`:
  `[propext]`, which is permitted by I7.
- `sorry`/`sorryAx`/`admit` added: none.
- Full hygiene audit: green across 564 project declarations.

## CORRESPONDENCE rows touched
- Updated the Issue 3 taxonomy row to `ISA.OperationClass` and made the
  class-level scope explicit.
- Recorded the pending read-equation paper-pin discrepancy for George's
  fidelity review.

## Adversarial review
- Dimensions checked: issue scope, paper fidelity, fixed-program selection,
  read/write memory equations, non-vacuity, public-surface size, competing step
  relations, documentation claims, axioms, and source hygiene.
- **Confirmed and addressed:** the generic name `Operation` obscured the
  class-level abstraction; a catch-all branch made future memory behavior too
  easy to add silently; the paper pin predates the explicit unchanged-memory
  read correction.
- **Suspected:** none remaining in the Issue 3 scope.
- No source probes were added to the worktree.

## Build at end
- `lake build`: green (8,593 jobs).
- Full CI audit: green; all 38 audited correspondence declarations elaborate,
  and only the permitted axioms occur.

## Handoff note
- George's human review must confirm the five-class simplification and the
  interpretation of `code` as a class map. The team should separately decide
  when to advance `docs/PAPER_REVISION.md` from `a0f5e0b` to a revision that
  includes the read correction.
- The worktree remains uncommitted and unpushed for Yavor's review.
