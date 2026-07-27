# Axiom Audit

> **Document status on `yl-memory-reconstruction`: historical,
> branch-specific audit.** Several declaration names below belong to
> `yl-bus-modifications-draft`. The current audit for this branch is recorded
> in `MEMORY_RECONSTRUCTION.md` and should be used for present claims.

## Scope

This records the declaration-level `#print axioms` result for the main current
theorems. Importing Mathlib makes many classical results available, but does not
mean every theorem depends on them; `#print axioms` follows each declaration's
actual proof dependencies.

Current-branch audit date: 2026-07-22.

Pinned toolchain:

```text
leanprover/lean4:v4.32.0-rc1
mathlib v4.32.0-rc1
```

## Reproduction

Run `lake env lean --stdin` from the repository root and provide:

```lean
import VanillaZkVM
#print axioms VanillaZkVM.Bus.System.segment_valid_or_collision
#print axioms VanillaZkVM.Bus.System.segment_extract
#print axioms VanillaZkVM.Bus.System.segment_knowledgeSound
#print axioms VanillaZkVM.TwoStep.System.cte
#print axioms VanillaZkVM.knowledgeSound_trivialAS
#print axioms VanillaZkVM.Sanity.alwaysAcceptEmpty_not_knowledgeSound
#print axioms VanillaZkVM.Sanity.constantBoolHash_not_collisionResistant
#print axioms VanillaZkVM.Sanity.acceptAllVC_not_positionBinding
```

## Results

| Declaration | Reported axioms |
|---|---|
| `Bus.System.segment_valid_or_collision` | none |
| `Bus.System.segment_extract` | none |
| `Bus.System.segment_knowledgeSound` | none |
| `TwoStep.System.cte` | `propext`, `Quot.sound` |
| `knowledgeSound_trivialAS` | none |
| `Sanity.alwaysAcceptEmpty_not_knowledgeSound` | none |
| `Sanity.constantBoolHash_not_collisionResistant` | none |
| `Sanity.acceptAllVC_not_positionBinding` | none |

`TwoStep.System.cte` relies on standard Lean/Mathlib propositional extensionality
and quotient soundness through its imported rewriting/arithmetic proof. None of
the audited declarations reports `Classical.choice`. This audit says nothing
about semantic adequacy or cryptographic realism; it only identifies logical
axioms in the compiled proof terms.

## Experimental memory branch

`origin/memory-integration` at `bd48832` was independently built and audited on
2026-07-25. These declarations are not yet present on the current Bus branch:

| Declaration | Reported axioms |
|---|---|
| `mem_eq_of_commit_eq` | `Quot.sound` |
| `step_mem_extract` | `propext`, `Classical.choice`, `Quot.sound` |
| `commit_update` | none |
| `commitInv_write` | none |

The `Classical.choice` dependency comes from the generic point-update used by
`step_mem_extract` without a `DecidableEq VC.Index` instance. A scratch
pre-invariant-only reconstruction theorem using `[DecidableEq VC.Index]`
compiled with no axioms; its intended interface is recorded in
`MEMORY_INVARIANT_REVIEW.md`.

## Policy

- Rerun this audit after changes to any theorem, dependency, or toolchain.
- CI should fail on newly introduced `sorry`/`admit` and should display axiom
  changes for human review.
- Standard axioms are not automatically forbidden, but additions must be
  explained in the proof contract.
- Before a public milestone, repeat the audit on a stable Lean/Mathlib release.
