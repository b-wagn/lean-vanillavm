<!--
Copy this file to docs/sessions/<YYYY-MM-DD>-<issue-slug>.md at the start of a
substantial (especially autonomous, I11) session and fill it in as you go. One
entry per session; keep it short. This is what makes multi-person / multi-agent
work resumable (finality pattern; CONVENTIONS.md §8).
-->

# Session <YYYY-MM-DD> — <issue-slug> (Issue N)

## Bootstrap
- **Issue:** PLAN.md → Issue N (<title>).
- **Branch:** `<branch>` off `main-temp`.
- **Read at start:** INVARIANTS.md, CONVENTIONS.md, <any issue-specific docs>.
- **Build at start:** `lake build` green? (yes/no) — commit `<sha>`.

## What changed
- <bullet per meaningful change: file, declaration, why.>
- New public surface (I5): <list every new public def, or "none">.

## Axiom / `sorry` ledger diff
- `#print axioms <headline>` before: <axioms> / after: <axioms>.
- `sorry`/`admit` added: <none, or the tracked allowlist with justification (I7)>.

## CORRESPONDENCE rows touched
- <row(s) added/changed and their new status>.

## Adversarial review (if run — SKILLS/adversarial-review.md)
- Dimensions run: (a) vacuity (b) kernel-truth (c) CI (d) docs.
- CONFIRMED findings: <with reproduction, or "none">.
- SUSPECTED (unreproduced): <or "none">.
- Probes reverted, `git status` clean: (yes/no).

## Build at end
- `lake build` green? (yes/no) — commit `<sha>`.

## Handoff note
- <what a next session / reviewer needs to know to pick this up.>
