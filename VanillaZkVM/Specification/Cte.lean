import VanillaZkVM.Preliminaries.ArgumentSystem
import VanillaZkVM.Specification.Zkvm

/-!
# Correct-trace extractability — the specification (the abstract heart)

This is the central file: what an abstract `ZkVM` (from `Zkvm.lean`) is *meant to
prove*, and its equivalence with the frozen knowledge-soundness notion.

## Main definitions
* the correct-execution relation `Rstar` the system is meant to prove, and the
  final argument system `ASstar` viewed as an argument system for it;
* correct-trace extractability `CTE`, stated in VM-native terms.

## Main results
* The keystone theorem `cte_iff_knowledgeSound`:
  `CTE V ↔ KnowledgeSound V.ASstar`.

Concrete systems (the two-step toy in `VMs/TwoStep/`, later the full vanilla VM)
instantiate `ZkVM` and prove `CTE` — typically by proving `KnowledgeSound ASstar`
and invoking the equivalence.
-/

namespace VanillaZkVM

namespace ZkVM

variable (V : ZkVM)

/-- The correct-execution relation `R*`: statements are boundary claims,
witnesses are traces, membership is trace validity.

Paper: `eq:relation-star`. -/
def Rstar : Relation where
  Stmt := V.Stmt
  Wit := ℕ → V.State
  rel := fun x tr => V.TraceValid x tr

/-- The system's final argument system, viewed as an argument system for `R*`. -/
def ASstar : ArgumentSystem V.Rstar where
  Proof := V.Proof
  verify := V.verify

/-- **Correct-trace extractability** (VM-native form): a single trace-extractor
turns every accepting proof into a valid `T`-step execution of the claim.

Paper: `def:cte` at the revision pinned in `docs/PAPER_REVISION.md`. This is its
perfect, probability-free core: PPT/probability bookkeeping is out of scope (I8),
and the full-memory boundary commitment equations belong to a concrete VM instance
rather than to this abstract statement. -/
def CTE : Prop :=
  ∃ E : V.Stmt → V.Proof → (ℕ → V.State),
    ∀ (x : V.Stmt) (p : V.Proof), V.verify x p → V.TraceValid x (E x p)

/-- **Keystone.** Correct-trace extractability is exactly knowledge soundness of
the final argument system for the correct-execution relation `R*`. The proof is
structural: both sides are "∃ extractor, ∀ accepting (x, p), the output is a
valid trace", differing only in packaging the extractor as a bare function versus
an `Extractor` record.

Paper: `rem:cte-ks`. -/
theorem cte_iff_knowledgeSound : V.CTE ↔ KnowledgeSound V.ASstar := by
  constructor
  · rintro ⟨E, hE⟩
    refine ⟨⟨E⟩, ?_⟩
    intro x p hp
    exact hE x p hp
  · rintro ⟨E, hE⟩
    refine ⟨E.extract, ?_⟩
    intro x p hp
    exact hE x p hp

end ZkVM

end VanillaZkVM
