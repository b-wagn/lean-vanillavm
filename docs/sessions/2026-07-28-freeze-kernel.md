# Session 2026-07-28 — freeze-kernel (Issue 0)

## Bootstrap
- **Issue:** PLAN.md → Issue 0 (Freeze the core *kernel* & stand up review scaffolding).
- **Branch:** `freeze-kernel` off `main-temp`.
- **Read at start:** INVARIANTS.md, CONVENTIONS.md, PLAN.md, CORRESPONDENCE.md.
- **Build at start:** `lake build` green (exit 0). Baseline `#print axioms`:
  - `ZkVM.cte_iff_knowledgeSound` — no axioms.
  - `knowledgeSound_trivialAS` — no axioms.
  - `chain_flatten` — `[propext, Quot.sound]`.
  - `TwoStep.System.cte` — `[propext, Quot.sound]`.

## What changed (initial pass; later review continuation below)
- **Crypto.lean → definitions only**, split into `## Frozen kernel (I4)` (`Relation`,
  `ArgumentSystem`, `Extractor`, `KnowledgeSound`) and `## Provisional` (`VectorCommitment`,
  `PositionBinding`, `PuncturedBinding`, `HashCommitment`, `CollisionResistant`), each
  provisional def carrying a `provisional` docstring note (I4).
- **`trivialAS` + `knowledgeSound_trivialAS` moved out** to new `CryptoSanity.lean`
  (the I6 non-vacuity floor, kept out of the defs file).
- **`concatTrace` + `chain_flatten` moved out** of `Zkvm.lean` to new `Trace.lean`
  (a generic helper — not part of the frozen kernel). `Twostep.lean` gains
  `import VanillaZkVM.Trace`. Root module imports the two new files.
- **Scaffolding created:** `SKILLS/adversarial-review.md`, `docs/sessions/TEMPLATE.md`,
  `docs/LESSONS_LEARNED.md`, `VanillaZkVM/math-companion.md` (kernel definitions on paper).
- **CI created:** `.github/workflows/ci.yml` + `scripts/ci_checks.py` — `lake build`,
  a CORRESPONDENCE row-elaboration check (I1), and a `#print axioms` gate (I7).
- New public surface (I5): **none added** — this issue *reduces* surface. Same
  declarations, reorganized across files; `trivialAS`/`knowledgeSound_trivialAS`/
  `concatTrace`/`chain_flatten` keep their fully-qualified names.

## Axiom / `sorry` ledger diff
- No `sorry`/`admit` added. Axiom footprints unchanged from baseline (pure reorganization).

## CORRESPONDENCE rows touched
- In this initial pass, no row content changed; all named declarations kept their
  qualified names and elaborated. This status was superseded by Dmitry's 2026-07-29
  review and the continuation below.

## Build at end
- `lake build`: green (exit 0). CI checks (`ci_checks.py`): both pass — 17 CORRESPONDENCE
  declarations elaborate; headline axioms unchanged (`cte_iff_knowledgeSound` and
  `knowledgeSound_trivialAS` axiom-free; `chain_flatten` and `TwoStep.System.cte` use
  `[propext, Quot.sound]`), all within the permitted set.

## Handoff note
- This was the handoff from the initial pass. Its proposed special Benedikt/George
  joint-ratification gate was withdrawn by Dmitry on 2026-07-29; see the continuation
  below. Nothing was committed during that pass (CONVENTIONS §4).
- Each Crypto.lean rebuild costs ~13 min (it `import Mathlib`); batch edits before building.

---

## Review continuation — 2026-07-29

### Bootstrap
- **Branch/worktree:** `yl-issue-0-review-fixes`, based exactly on
  `origin/freeze-kernel@5471ce5`.
- **Read at start:** README, INVARIANTS, CONVENTIONS, PLAN, CORRESPONDENCE,
  math companion, Issue #6, PR #16, and the dependent Issues #7/#9/#11.
- **Build at start:** `lake build` green (8,587 jobs).
- **Audit at start:** the original full audit green (16 correspondence declarations,
  403 project declarations).

### Accepted review feedback and bounded response
- **Paper rows remain paper-keyed.** Per Dmitry, no artificial correspondence rows were
  added for Lean infrastructure without an explicit paper definition. Existing tier
  metadata was corrected (`knowledgeSound_trivialAS` = scaffolding, VM state = support,
  `HashCommitment` = provisional).
- **Paper correction recorded.** Dmitry accepted the fixed-`T` correction;
  `docs/PAPER_REVISION.md` provisionally records
  `zkvm-whitepaper@a0f5e0b63395a2fddce3f949c4de1df9264a174b`. That correction fixes
  program code and `T` as system parameters, matching the existing frozen `ZkVM.T : Nat`;
  no hidden kernel-signature change was made. The exact hash remains a PR-review item.
- **Completeness claim narrowed.** `Rstar` is marked incomplete until Issue 7 supplies
  the outer full-memory/commitment boundary equations from `eq:relation-star`.
- **Step contract added.** Three public Lean-only coordination definitions were added:
  `StepInterface`, `StepInterface.MemoryBridge`, and `StepInterface.BusBridge`.
  `ZkVM.step` remains the sole plain predicate. An accepting private Boolean-toggle
  one-step model satisfies CTE and both bridges with equality as its representation
  invariant.
- **I7 coverage repaired.** The audit now inventories root `VanillaZkVM.lean` plus every
  submodule, explicitly builds and imports every discovered module, detects direct
  `sorryAx`, ignores comments/string literals while preserving line numbers, and has
  built-in regression tests.
- **Special review gate removed.** PLAN and CONVENTIONS no longer require immediate joint
  Benedikt/George ratification for Issue 0. Ordinary collaborator review and Issue 9's
  independent audit remain.

### Public surface and constitutional diff
- New public source declarations (I5): exactly 3, all in `Step.lean`; the
  `StepInterface` structure's three projections are its documented field API.
- I4 was amended explicitly to freeze those three interface signatures.
- No existing declaration changed type or semantics.

### Axiom / `sorry` ledger
- No `axiom`, `sorry`, `admit`, or `native_decide` added.
- The permitted axiom set remains `{propext, Classical.choice, Quot.sound}`.

### Pre-commit handoff
- The worktree was deliberately kept **uncommitted and unpushed** while Yavor reviewed
  the complete diff. The continuation commit follows his requested second-pass audit.
- The live GitHub Issue #6 description still contains the withdrawn special
  Benedikt/George ratification requirement. Repository scope is governed by PLAN (I2);
  the issue text should be updated separately so the two surfaces agree.

### Final build and audit
- `lake build`: green (8,589 jobs).
- Full audit: green; 9 project sources inventoried and explicitly built, 16 audited
  correspondence declarations elaborated, and 426 project declarations inspected.
- Axiom footprints:
  - `ZkVM.cte_iff_knowledgeSound` — none.
  - `knowledgeSound_trivialAS` — none.
  - `chain_flatten` — `[propext, Quot.sound]`.
  - `TwoStep.System.cte` — `[propext, Quot.sound]`.

### Adversarial gate probes (all reverted)
- Root `VanillaZkVM.lean` anonymous `example : False := by sorry`: rejected by
  the source layer at the correct line.
- Root unused `axiom ... : False`: rejected by both source and module layers.
- Unimported `VanillaZkVM/CIProbe.lean` using direct `sorryAx`: bare `lake build`
  still passed (confirming the original default-target gap), while the full audit
  explicitly built the module and rejected it in both layers.
- The same unimported module containing only the string
  `"sorry axiom sorryAx admit native_decide"`: accepted, explicitly built, and
  inspected.
- Deliberately renamed audited correspondence declaration: rejected as an unknown
  Lean identifier.
- All `CIProbe`/root/table mutations were removed; `git diff --check` passes and
  the only worktree changes are this intended, uncommitted Issue 0 draft.
