import VanillaZkVM.Preliminaries.ArgumentSystem

/-!
# Consistency-floor models for the argument-system kernel

Non-vacuity witnesses (`docs/INVARIANTS.md` I6) for the definitions in
`ArgumentSystem.lean`, kept out of the definitions file so the kernel is
definitions only.

## Main definitions
* `trivialAS` — the honest degenerate argument system for any relation.

## Main results
* `knowledgeSound_trivialAS` — it is knowledge-sound, so `KnowledgeSound` is
  satisfiable (not `False`).
-/

namespace VanillaZkVM

/-- The **trivial argument system** for `R`: a "proof" is literally a witness, and
`verify x w` just checks membership `(x; w) ∈ R`. This is the honest degenerate
argument — no succinctness, no hiding. Used only to witness satisfiability of
`KnowledgeSound`. -/
def trivialAS (R : Relation) : ArgumentSystem R where
  Proof := R.Wit
  verify := fun x w => R.rel x w

/-- **Non-vacuity of `KnowledgeSound`.** `KnowledgeSound` is an idealized
assumption. Here we discharge the worry — that it might be unsatisfiable, making
every `KnowledgeSound … → …` theorem vacuously true — by exhibiting a model:
`trivialAS` is knowledge-sound, with the identity extractor. This is a consistency
floor, not a security guarantee: it shows the assumption is not `False`, not that
any real (succinct) SNARK meets it. -/
theorem knowledgeSound_trivialAS (R : Relation) : KnowledgeSound (trivialAS R) :=
  ⟨⟨fun _ w => w⟩, fun _ _ h => h⟩

end VanillaZkVM
