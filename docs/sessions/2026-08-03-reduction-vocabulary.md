# Session 2026-08-03 — reduction-vocabulary (Issue 2)

> **Superseded in part (2026-08-07).** The *algorithmic, unkeyed* `CollisionResistant`
> recorded below was later replaced by a **keyed, finder-based** one; `Cost.lean`/`Alg`
> and `crAssumption_holds_iff` were dropped, and `crAssumption` gained a key argument.
> The reduction vocabulary itself (`ExtractOrBreak`/`ReducesTo`/
> `knowledgeSound_of_extractOrBreak`) is unchanged in substance, though `Assumption`
> was later renamed to `HardnessAssumption` (2026-08-10). See
> `2026-08-07-keyed-cr.md`. This ledger is kept as the historical record of that session.

## Bootstrap
- **Issue:** PLAN.md → Issue 2 (Reduction vocabulary + extract-or-break refactor).
- **Branch:** `reduction-vocabulary` off `main-temp`.
- **Read at start:** INVARIANTS.md, CONVENTIONS.md, PLAN.md (Issue 2), CORRESPONDENCE.md;
  reused `extract-or-collision` / `cr-algorithmic` (Jessica's prior branches).
- **Build at start:** `lake build` green — commit `8e2bebb` (main-temp head).

## What changed
- **`Reduction.lean` (new).** The extract-or-break vocabulary: `Assumption`
  (`Break` + `IsBreak`), `Assumption.Holds`, `ExtractOrBreak` (witness-extractor
  `E` + **break-extractor `B`**, both plain functions), and the corollary
  `knowledgeSound_of_extractOrBreak`. Worked instance `crAssumption` (CR as an
  assumption; break = colliding pair) + `crAssumption_holds_iff`.
- **`Cost.lean` (new).** Minimal `Alg` (function + abstract `cost`) — only for the
  algorithmic collision-finder; no combinators (deferred to Issue 6/8).
- **`Crypto.lean`.** `CollisionResistant` restated **algorithmically** ("no finder
  algorithm outputs a collision") — provisional layer, allowed by I4. Import
  `VanillaZkVM.Cost`.
- **`CryptoSanity.lean`.** `collisionResistant_iff_injective` (algorithmic ⟺
  injectivity) and non-vacuity model `idHashCommitment` /
  `collisionResistant_idHashCommitment`.
- **`Bus.lean`.** `segment_extract` → `segment_extract_or_collision` (an
  `ExtractOrBreak` instance against `crAssumption`; `Assumptions` drops `busCR`) +
  corollary `segment_knowledgeSound` via the generic vocabulary. Prototype layer —
  redone in Issue 5; this only demonstrates the shape.
- **New public surface (I5):** `Reduction.{Assumption, Assumption.Holds,
  ExtractOrBreak, knowledgeSound_of_extractOrBreak, crAssumption,
  crAssumption_holds_iff}`; `Cost.Alg`; `CryptoSanity.{collisionResistant_iff_injective,
  idHashCommitment, collisionResistant_idHashCommitment}`. The 3-def vocabulary
  core is `Assumption` / `Assumption.Holds` / `ExtractOrBreak`.

## Axiom / `sorry` ledger diff
- `#print axioms` after:
  - `Reduction.knowledgeSound_of_extractOrBreak`, `Reduction.crAssumption_holds_iff`:
    **no axioms**.
  - `Bus.System.segment_extract_or_collision`, `Bus.System.segment_knowledgeSound`,
    `collisionResistant_iff_injective`, `collisionResistant_idHashCommitment`:
    `[propext, Classical.choice, Quot.sound]` (⊆ permitted set, I7).
- `sorry`/`sorryAx`/`admit` added: none.

## CORRESPONDENCE rows touched
- `advantage / reduction vocabulary` → `Reduction.*` now **stated/proved** (was planned).
- `bus unification / extract-or-collision` → shape **proved** as
  `Bus.System.segment_extract_or_collision` (wiring still Issue 5).
- `Collision resistance (Adv^cr)` → now the **algorithmic** form; row reset to
  `_unreviewed_` pending Dmitry re-sign (provisional layer, I4).

## Adversarial review
- Not run this session (left for the pre-PR audit).

## Build at end
- `lake build` green. Uncommitted on `reduction-vocabulary` (awaiting review/commit).

## Handoff note
- Reviewer (Dmitry, per Issue 2): bless the extract-or-break *shape* — does `B`
  compose across layers, and is the `crAssumption` break a genuine assumption
  break? Re-sign the CR row (now algorithmic). Remaining before PR: `/simplify` on
  the diff, `/security-review` on the new definitions, adversarial-review pass.
- The Bus instance is on the prototype layer; Issue 5 rebuilds it over the frozen
  kernel — treat `segment_extract_or_collision` as a shape demonstration, not the
  final wiring.
