import VanillaZkVM.Crypto  -- base import (brings in Mathlib); no crypto defs are used here

/-!
# A cost model for tight reductions with explicit constants

The minimal cost-accounting needed to state **exact** reduction costs. A
cost-annotated algorithm bundles a function with a step-count `cost`; the three
composition combinators **add** costs, reflecting straight-line execution with no
rewinding. `share` additionally models reusing an intermediate result, so a shared
prefix is charged exactly once.

There is deliberately **no asymptotic layer** here (`IsPoly`, `Polynomial`,
`Sized` are all gone): every reduction cost below is an exact closed form with
explicit constants, which is what a tight reduction needs.
-/

namespace VanillaZkVM

/-- A cost-annotated algorithm `α → β`: the function `run` together with a
step-count `cost`. No machine model is fixed; `cost` is an abstract accounting a
concrete instance must justify. -/
structure Alg (α β : Type) where
  run : α → β
  cost : α → ℕ

namespace Alg

variable {α β γ δ : Type}

/-- Sequential composition: run `f`, then `g`; costs **add** (straight-line, no
rewinding). -/
def comp (g : Alg β γ) (f : Alg α β) : Alg α γ where
  run := g.run ∘ f.run
  cost := fun a => f.cost a + g.cost (f.run a)

/-- Fan-out: run `f` and `g` on the same input and pair the results; costs add
(each is run once, from scratch). -/
def pair (f : Alg α β) (g : Alg α γ) : Alg α (β × γ) where
  run := fun a => (f.run a, g.run a)
  cost := fun a => f.cost a + g.cost a

/-- **Shared** fan-out: run `f` *once*, feed its result to both `g` and `h`, and
pair the outputs. Unlike `(g.comp f).pair (h.comp f)`, the shared prefix `f` is
charged a **single** time — the honest cost of a straight-line reduction that
reuses an intermediate result. -/
def share (f : Alg α β) (g : Alg β γ) (h : Alg β δ) : Alg α (γ × δ) where
  run := fun a => (g.run (f.run a), h.run (f.run a))
  cost := fun a => f.cost a + g.cost (f.run a) + h.cost (f.run a)

/-- Run `g` on the `m` derived inputs `idx a 0, …, idx a (m-1)` and collect the
results as a function `ℕ → β` (only the first `m` are meaningful). The cost is the
**sum** of the per-item costs — a straight-line loop over the `m` segments, no
shared re-work. This is the many-item generalisation of `pair`. -/
def seqRange (m : ℕ) (idx : α → ℕ → γ) (g : Alg γ β) : Alg α (ℕ → β) where
  run := fun a i => g.run (idx a i)
  cost := fun a => ∑ i ∈ Finset.range m, g.cost (idx a i)

end Alg
end VanillaZkVM
