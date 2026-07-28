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

## What changed (Phases 0–C; Phase D is human review, not done here)
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
- No row content changed; all named declarations keep their qualified names and still
  elaborate. The kernel rows remain `_unreviewed_` pending Phase D (Benedikt + George).

## Build at end
- `lake build`: green (exit 0). CI checks (`ci_checks.py`): both pass — 17 CORRESPONDENCE
  declarations elaborate; headline axioms unchanged (`cte_iff_knowledgeSound` and
  `knowledgeSound_trivialAS` axiom-free; `chain_flatten` and `TwoStep.System.cte` use
  `[propext, Quot.sound]`), all within the permitted set.

## Handoff note
- **Phase D (not done — the actual point of Issue 0):** Benedikt + George read the entire
  frozen kernel and jointly ratify the abstractions, then sign the Core/frozen-kernel rows
  in CORRESPONDENCE.md (fill `Fidelity`/`Complete`/`Reviewer`).
- Nothing committed (CONVENTIONS §4 — commit only when a human asks). `VanillaZkVM/tmp.md`
  left untracked (Dmitry's project-seed notes). `docs/hicks-digest.md` still untracked but
  referenced by INVARIANTS.md — consider tracking it.
- Each Crypto.lean rebuild costs ~13 min (it `import Mathlib`); batch edits before building.
