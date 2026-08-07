# Session 2026-08-07 — Issue-1 review follow-up (Issue 1)

## Bootstrap
- **Issue:** PLAN.md → Issue 1 (committed memory to full-memory CTE).
- **Branch:** `yl-issue-1`, based on `main-temp`.
- **Read at start:** INVARIANTS.md, CONVENTIONS.md, PLAN.md,
  CORRESPONDENCE.md, STEP_INTERFACES.md, MEMORY_RECONSTRUCTION.md, the math
  companion, and all PR #17 commits and review messages through `1906de6`.
- **Build at start:** the PR job's `lake build` passed at `1906de6`; its audit
  failed because `scripts/ci_checks.py` still named the removed theorem
  `TwoStep.System.cte_full`.

## What changed
- Deleted the unaudited `Bus.lean` playground module and removed its umbrella
  import. Living documentation now records that Issue 5 starts from no active
  bus implementation; the deleted file remains available in git history.
- Updated the CI headline list to the current
  `cte_committedMemory`/`cte_fullMemory` names.
- Replaced review-flagged shorthand with formal names or direct statements of
  the relevant equations (`MemStep`, `CommitInv`, `CommittedMemory.step`, and
  `StepInterface.MemoryBridge`).
- Expanded the comments for the key Issue-1 definitions and bridge theorems so
  they explain in ordinary language what each proposition asserts, what data it
  assumes, and why the result is needed for trace reconstruction.
- Renamed one private sanity theorem so its name states the property it proves:
  `appendBitVC_openings_agree_away_from_update`.
- New public surface (I5): none. The only source-surface removal is the
  unaudited Bus prototype.

## Axiom / `sorry` ledger diff
- Headline footprints are unchanged and remain subsets of
  `{propext, Classical.choice, Quot.sound}`.
- `sorry`/`sorryAx`/`admit`/`native_decide`/new `axiom` added: none.

## CORRESPONDENCE rows touched
- Removed the obsolete prototype Bus rows. The corresponding paper items now
  appear only in the Planned table with names deferred to Issue-5 definition
  review.
- Issue-1 row statuses and reviewer fields are unchanged.

## Adversarial review
- Not run; this follow-up changes documentation, CI names, and removes an
  explicitly unaudited module. The complete repository audit was run instead.

## Build at end
- `lake build`: green (8,591 jobs).
- `ci_checks.py --self-test --check-correspondence --check-axioms
  --check-hygiene`: green (11 modules, 33 correspondence declarations, 479
  project declarations inspected).

## Handoff note
- Changes remain uncommitted for Yavor's review. After approval, commit and
  push them, then synchronize the PR description with the final terminology,
  Bus deletion, theorem names, and validation counts.
