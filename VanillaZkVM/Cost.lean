import VanillaZkVM.Crypto

/-!
# A lightweight cost model for straight-line reductions (level-B prototype)

`Crypto.lean` models extractors as *bare functions* with no complexity content, so
"the reduction is efficient" is a meta-level claim, not a checked theorem. This
file is a proportionate ("level B") fix: tag algorithms with an abstract cost,
define polynomial-time, and prove that the reduction's efficiency *composes* from
its parts — without building a full machine model.

The key modeling points:

* `Alg` bundles a function with a `cost`. Sequential composition **adds** costs
  (`Alg.comp`) — this is exactly what makes straight-line extraction efficient:
  the reduction runs each sub-extractor once, in sequence, with *no rewinding*, so
  the blow-up is additive, not multiplicative.
* `IsPoly` bounds **both** the cost and the *output size* by a polynomial in the
  input size. Bundling the output-size bound is what makes `IsPoly` closed under
  composition (a poly-time stage feeds poly-size inputs to the next).
* `KnowledgeSoundE` / `KnowledgeSoundUpToCollisionE` are the efficient
  counterparts of the perfect notions: the extractor/reduction must be `IsPoly`.
* `reduction_isPoly` is the payoff: a reduction built as a fan-out of finitely
  many poly extractors followed by poly glue is poly — proved in one line from the
  closure lemmas. This is the shape of `Bus.segment_extract`'s reduction.
-/

namespace VanillaZkVM

/-! ## Size and cost-annotated algorithms -/

/-- A type equipped with a size measure (e.g. bit-length of a representation). -/
class Sized (α : Type) where
  size : α → ℕ

open Sized

instance : Sized ℕ := ⟨id⟩
instance {α β} [Sized α] [Sized β] : Sized (α × β) := ⟨fun p => size p.1 + size p.2⟩
instance {α β} [Sized α] [Sized β] : Sized (α ⊕ β) :=
  ⟨fun s => match s with | .inl a => size a | .inr b => size b⟩

/-- A cost-annotated algorithm `α → β`: the function `run` together with a
step-count `cost`. No machine model is fixed; `cost` is an abstract accounting a
concrete instance must justify. -/
structure Alg (α β : Type) where
  run : α → β
  cost : α → ℕ

namespace Alg

variable {α β γ : Type}

/-- Sequential composition: run `f`, then `g`. Costs **add** (straight-line, no
rewinding). -/
def comp (g : Alg β γ) (f : Alg α β) : Alg α γ where
  run := g.run ∘ f.run
  cost := fun a => f.cost a + g.cost (f.run a)

/-- Fan-out: run `f` and `g` on the same input and pair the results; costs add. -/
def pair (f : Alg α β) (g : Alg α γ) : Alg α (β × γ) where
  run := fun a => (f.run a, g.run a)
  cost := fun a => f.cost a + g.cost a

end Alg

/-! ## Polynomial-time -/

/-- `f` is **polynomial-time**: both its cost and its output size are bounded by a
polynomial in the input size. The output-size clause is what makes the class
compose. -/
structure IsPoly {α β} [Sized α] [Sized β] (f : Alg α β) : Prop where
  costPoly : ∃ p : Polynomial ℕ, ∀ a, f.cost a ≤ p.eval (size a)
  sizePoly : ∃ p : Polynomial ℕ, ∀ a, size (f.run a) ≤ p.eval (size a)

/-- Evaluation of an `ℕ`-coefficient polynomial is monotone in its argument. -/
theorem evalNat_mono (p : Polynomial ℕ) {m n : ℕ} (h : m ≤ n) : p.eval m ≤ p.eval n := by
  induction p using Polynomial.induction_on' with
  | add q r hq hr => simp only [Polynomial.eval_add]; exact Nat.add_le_add hq hr
  | monomial k a =>
      simp only [Polynomial.eval_monomial]
      exact Nat.mul_le_mul (le_refl a) (Nat.pow_le_pow_left h k)

namespace IsPoly

variable {α β γ : Type}

/-- The identity algorithm (cost `0`) is polynomial. -/
theorem id_ [Sized α] : IsPoly (⟨id, fun _ => 0⟩ : Alg α α) where
  costPoly := ⟨0, by intro a; simp⟩
  sizePoly := ⟨Polynomial.X, by intro a; simp⟩

/-- **Composition preserves poly-time** (costs add). -/
theorem comp [Sized α] [Sized β] [Sized γ]
    {g : Alg β γ} {f : Alg α β} (hg : IsPoly g) (hf : IsPoly f) :
    IsPoly (g.comp f) where
  costPoly := by
    obtain ⟨pf, hpf⟩ := hf.costPoly
    obtain ⟨pg, hpg⟩ := hg.costPoly
    obtain ⟨of, hof⟩ := hf.sizePoly
    refine ⟨pf + pg.comp of, fun a => ?_⟩
    calc (g.comp f).cost a
        = f.cost a + g.cost (f.run a) := rfl
      _ ≤ pf.eval (size a) + pg.eval (size (f.run a)) := Nat.add_le_add (hpf a) (hpg _)
      _ ≤ pf.eval (size a) + pg.eval (of.eval (size a)) :=
            Nat.add_le_add_left (evalNat_mono pg (hof a)) _
      _ = (pf + pg.comp of).eval (size a) := by rw [Polynomial.eval_add, Polynomial.eval_comp]
  sizePoly := by
    obtain ⟨of, hof⟩ := hf.sizePoly
    obtain ⟨og, hog⟩ := hg.sizePoly
    refine ⟨og.comp of, fun a => ?_⟩
    calc size ((g.comp f).run a)
        = size (g.run (f.run a)) := rfl
      _ ≤ og.eval (size (f.run a)) := hog _
      _ ≤ og.eval (of.eval (size a)) := evalNat_mono og (hof a)
      _ = (og.comp of).eval (size a) := by rw [Polynomial.eval_comp]

/-- **Fan-out preserves poly-time** (costs and output sizes add). -/
theorem pair [Sized α] [Sized β] [Sized γ]
    {f : Alg α β} {g : Alg α γ} (hf : IsPoly f) (hg : IsPoly g) :
    IsPoly (f.pair g) where
  costPoly := by
    obtain ⟨pf, hpf⟩ := hf.costPoly
    obtain ⟨pg, hpg⟩ := hg.costPoly
    refine ⟨pf + pg, fun a => ?_⟩
    calc (f.pair g).cost a = f.cost a + g.cost a := rfl
      _ ≤ pf.eval (size a) + pg.eval (size a) := Nat.add_le_add (hpf a) (hpg a)
      _ = (pf + pg).eval (size a) := by rw [Polynomial.eval_add]
  sizePoly := by
    obtain ⟨of, hof⟩ := hf.sizePoly
    obtain ⟨og, hog⟩ := hg.sizePoly
    refine ⟨of + og, fun a => ?_⟩
    calc size ((f.pair g).run a)
        = size (f.run a) + size (g.run a) := rfl
      _ ≤ of.eval (size a) + og.eval (size a) := Nat.add_le_add (hof a) (hog a)
      _ = (of + og).eval (size a) := by rw [Polynomial.eval_add]

end IsPoly

/-! ## Efficient security notions -/

/-- **Efficient** (perfect) knowledge soundness: the straight-line extractor is a
*polynomial-time* algorithm. -/
def KnowledgeSoundE {R : Relation} (AS : ArgumentSystem R)
    [Sized R.Stmt] [Sized AS.Proof] [Sized R.Wit] : Prop :=
  ∃ E : Alg (R.Stmt × AS.Proof) R.Wit, IsPoly E ∧
    ∀ x p, AS.verify x p → R.rel x (E.run (x, p))

/-- **Efficient** knowledge soundness *up to a collision* (unkeyed hash): a
polynomial-time reduction returning either a valid witness or an explicit
collision of `H`. The unkeyed CR assumption is that the `Sum.inr` branch is
computationally unrealizable. -/
def KnowledgeSoundUpToCollisionE {R : Relation} (AS : ArgumentSystem R)
    (H : HashCommitment)
    [Sized R.Stmt] [Sized AS.Proof] [Sized R.Wit] [Sized H.Domain] : Prop :=
  ∃ E : Alg (R.Stmt × AS.Proof) (R.Wit ⊕ (H.Domain × H.Domain)), IsPoly E ∧
    ∀ x p, AS.verify x p →
      (∀ w, E.run (x, p) = Sum.inl w → R.rel x w) ∧
      (∀ b b', E.run (x, p) = Sum.inr (b, b') → b ≠ b' ∧ H.hash b = H.hash b')

/-! ## The efficiency guarantee, abstractly -/

/-- **The reduction is efficient.** A reduction built as a fan-out of a bounded
number of polynomial extractors followed by polynomial glue is itself polynomial —
its cost is the *sum* of the parts' costs (straight-line: no rewinding blow-up).
This is the cost skeleton of `Bus.segment_extract`'s reduction: run the segment
extractor `E₁` and the inner-step extractor `E₂`, then O(1) bus-comparison glue
`G`. Extending `E₂` to the full fan-out of all four inner extractors is more
nested `pair`s — still poly by the same two lemmas. -/
theorem reduction_isPoly {S P W₁ W₂ O : Type}
    [Sized S] [Sized P] [Sized W₁] [Sized W₂] [Sized O]
    {E₁ : Alg (S × P) W₁} {E₂ : Alg (S × P) W₂} {G : Alg (W₁ × W₂) O}
    (h₁ : IsPoly E₁) (h₂ : IsPoly E₂) (hG : IsPoly G) :
    IsPoly (G.comp (E₁.pair E₂)) :=
  hG.comp (h₁.pair h₂)

end VanillaZkVM
