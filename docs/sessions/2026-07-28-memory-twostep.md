# Session 2026-07-28 — memory-twostep (Issue 1)

## Bootstrap
- **Issue:** PLAN.md → Issue 1 (Committed memory → `TwoStepWithMemory`; GitHub #7).
- **Branch:** `memory-twostep`, **rebased onto `origin/main-temp`** (584476e, the ratified
  freeze-kernel merge PR #16) after freeze-kernel landed with George's review. Earlier state
  (based on b89dd2a) preserved as `memory-twostep-pre-rebase`. Single clean Issue-1 commit.
- **Read at start:** PLAN.md, CONVENTIONS.md, CORRESPONDENCE.md, math-companion.md;
  `docs/issue1-implementation-proposal.md`; `Step.lean`/`ZkvmSanity.lean` (new Issue-0 contract);
  branches `memory-integration` (trunk) and `pr5` (sanity).
- **Compatibility with main-temp:** kernel API unchanged (Zkvm.lean gained only paper-anchor
  docstrings); the 4 drift conflicts (Crypto, CORRESPONDENCE, ci_checks, ci.yml) resolved toward
  main-temp's ratified versions + Issue-1 additions; redundant local gate commit dropped.
- **Build at start:** green (`origin/main-temp`).

## What changed
- `Crypto.lean`: added provisional defs `Complete`, `UpdateBinding`; **removed** `PuncturedBinding`;
  updated the frozen/provisional docstring. Kept definitions-only (no theorems).
- `Memory.lean` (NEW): ported from `memory-integration`; `mem_eq_of_commit_eq` relocated here (out of
  the defs-only kernel). Provides `FullVMState`, `CommitInv`, `MemStep`, `readC/writeC/readF/writeF`,
  `stepC/stepF`, `step_mem_extract`, `commit_update`, `commitInv_write`, `stepReconstruct`,
  `reconstructTrace`, `commitInv_step`, `trace_mem_extract`, `chooseDescr`(+`_spec`).
- `Twostep.lean`: opaque toy → classified toy. Imports `Memory` + `Trace` + `Step` (reuses the frozen
  `concatTrace`/`chain_flatten`, no local copy). Added `SegWitness.steps`, `stepRel`, `toCommitted`,
  `FinalStmtFull`, `toZkVMFull`, `traceValid_full`, `cte_full`. Kept the `Assumptions` trust-base
  record; `cte`/`cte_full` consume it.
- **`Twostep.lean` step-interface integration (NEW, satisfies the Issue-0 contract):**
  `stepInterface : StepInterface toZkVMFull` and `memoryBridge`, discharging
  `Step.StepInterface.MemoryBridge` via `step_mem_extract` ∘ `commitInv_step`. This is the concrete
  realization Issue-0's `Step.lean` named as the Issue-1 deliverable.
- `MemorySanity.lean` (NEW): ported `exactVC` (Complete/PositionBinding/UpdateBinding) and
  `appendBitVC` (Complete/PositionBinding); dropped the retired punctured-binding theorems. Break
  scaffolding (`UpdateBindingBreak`, `IsUpdateBindingBreak`, `UpdateBinding.not_isUpdateBindingBreak`)
  lives here, not in `Crypto.lean`. Headline separation: `appendBitVC_not_updateBinding`.
- `VanillaZkVM.lean`: added `Memory` and `MemorySanity` imports.
- Docs: `math-companion.md` §1 appended (+ provisional section updated); `CORRESPONDENCE.md` rows
  realized; `scripts/ci_checks.py` HEADLINE_THEOREMS += `trace_mem_extract`, `cte_full`.
- New public surface (I5): `Complete`, `UpdateBinding` (+ `UpdateBindingBreak`/`IsUpdateBindingBreak`),
  `FullVMState`, `CommitInv`, `MemStep`, `stepC`/`stepF`, `step_mem_extract`, `trace_mem_extract`,
  `toZkVMFull`, `cte_full`. `readC/writeC/readF/writeF`, `stepReconstruct`, `reconstructTrace`,
  `chooseDescr` are derived/internal.

## Axiom / `sorry` ledger diff
- `scripts/ci_checks.py --check-axioms` (green): `trace_mem_extract` and `cte_full` depend on
  `[propext, Classical.choice, Quot.sound]` — all permitted; `Classical.choice` from the
  `noncomputable`/`classical` reconstruction. No `sorryAx`.
- `sorry`/`admit` added: none.
- Fixed a latent Windows-only bug in `ci_checks.py`: `run_lean` now decodes subprocess output as
  utf-8 (the new theorems' `#check`/`#print axioms` output contains `Ŝ`/`π`/`φ`, which crashed the
  default cp1252 codec locally; the Linux CI runner was unaffected).

## CORRESPONDENCE rows touched
- Core: retired `PuncturedBinding` row; added `Complete`; realized `UpdateBinding` (proved).
- New "Memory extractability (Issue 1)" section: `CommitInv`, `mem_eq_of_commit_eq`, `stepC`/`stepF`,
  `step_mem_extract`, `trace_mem_extract`, `appendBitVC_not_updateBinding`.
- Two-step: added `cte_full`. Pruned the two realized rows from the Planned table.

## Adversarial review (SKILLS/adversarial-review.md) — run this session
Four dimensions, read-only skeptics (a,d) blind + orchestrator-run build-touching probes (b,c):
- **(a) Soundness/vacuity:** PASS. Bundle {Complete, PositionBinding, UpdateBinding, Assumptions,
  0<Nseg} jointly satisfiable — `exactVC` proves all three binding notions; `appendBitVC` fails
  UpdateBinding (two-sided witness). Every binding hypothesis does real work in the proofs; `cte`
  correctly takes none. No vacuity.
- **(b) Kernel-truth:** PASS. `Zkvm.lean` untouched (0 diff vs main-temp); Crypto.lean changed only
  the provisional tier (Complete/UpdateBinding added, PuncturedBinding removed); frozen kernel
  (Relation/ArgumentSystem/Extractor/KnowledgeSound) unchanged. Headline axioms = {propext,
  Classical.choice, Quot.sound}, no sorryAx.
- **(c) Gate integrity:** PASS. Injected probes confirmed the gates catch them: hygiene source scan
  flags `axiom`/`sorry`/`admit` (no FP on clean base); correspondence gate emits a renamed decl into
  the `#check` list → elaboration failure. All probes reverted; `git status` clean.
- **(d) Docs/overclaim:** 1 CONFIRMED finding, FIXED. The phrase "update binding is *strictly
  stronger than* position binding" (5 sites incl. a theorem docstring headline) overclaimed
  (asserts UpdateBinding ⟹ PositionBinding, which is unproved/false — proofs use hpos, hupd
  independently). Restated everywhere to "position binding does **not** imply update binding
  (a genuinely additional requirement)". Also: added `Paper: rem:mem-inheritance` to `memoryBridge`;
  added a "faithful but partial" scope note to the Memory-extractability CORRESPONDENCE section.
- SUSPECTED (unreproduced): none.
- Out-of-scope note (pre-existing, not this PR): `docs/paper-digest.md` still lists
  PositionBinding+PuncturedBinding as the live pair — a main-temp doc, left for a separate cleanup.
- Probes reverted, `git status` clean: yes.

## Build at end
- `lake build`: green (8591 jobs, exit 0). `python scripts/ci_checks.py --check-hygiene
  --check-correspondence --check-axioms`: green (post adversarial-review fixes). Committed on
  `memory-twostep` atop ratified `main-temp` (584476e).

## Handoff note
- Reconciliation used: trunk = `memory-integration`; `pr5` contributed only the sanity/break layer
  (its `UpdateBinding` is byte-identical). The reduction-*emitting* break form is deferred to Issue 6.
- Non-delegatable review (George): `UpdateBinding` ⇔ `def:binding`; that position binding does not
  imply it (separation `appendBitVC_not_updateBinding`) so it is a genuinely additional requirement;
  `CommitInv` is the right invariant; `memory-integration`↔`pr5` prove the same statement; run the
  vacuity probe.
- Committed as a single clean Issue-1 commit on `memory-twostep` atop ratified `main-temp` (584476e);
  backup of the pre-rebase state at `memory-twostep-pre-rebase`. Not pushed. `docs/paper-digest.md`
  (main-temp) still names PuncturedBinding as live — a separate, out-of-scope cleanup.
