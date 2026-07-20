import VanillaZkVM.Cost

/-!
# Efficient, unkeyed bus unification — the reduction's efficiency, discharged

This wires the cost layer (`Cost.lean`) into the security-critical step of the bus
architecture: **bus unification**. It proves, *end-to-end and with no `sorry`*,
that the unkeyed segment reduction is

* **correct** — on every accepting proof it outputs either a valid unified bus
  (satisfying both delegated predicates) or an *explicit* collision of `H`
  (no collision-resistance is assumed; the collision is produced), and
* **efficient** — the reduction is `IsPoly`, and this is *discharged* from the
  `IsPoly` of the sub-extractors via `IsPoly.comp`/`IsPoly.pair` (straight-line ⇒
  additive cost, no rewinding blow-up), not assumed.

## Why abstract carriers (the finitization caveat)

The concrete `Bus.lean`/`Zkvm.lean` witnesses are **infinite objects**:
`InnerStepWitness.states : ℕ → CommittedVMState`, and each state's
`regs : ℕ → Word`. Infinite data has no finite `size`, so "polynomial in input
size" is not even *definable* on those witnesses. Efficiency therefore only
becomes meaningful after finitizing the state model (finite registers
`Fin k → Word`, finite memory, `Fin`-indexed traces). This module works over
abstract `Sized` carrier types — exactly the interface such a finitization would
supply — so the theorem transfers verbatim once the model is finitized.

The representative shape is *step + one delegated chip* (one collision site).
Adding the other chips is more `pair`s and one more equality check per chip —
mechanically the same.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace VanillaZkVM
open Sized

namespace BusE

variable {H : HashCommitment}
variable {Stmt Proof IProof CProof : Type}
  [Sized Stmt] [Sized Proof] [Sized IProof] [Sized CProof]
  [Sized H.Domain] [Sized H.Digest]

/-! ## O(1) data-plumbing between stages, as polynomial algorithms -/

/-- Project the segment extractor's output to the inner-step verifier's input. -/
def Dstep : Alg (H.Digest × IProof × CProof) (H.Digest × IProof) :=
  ⟨fun t => (t.1, t.2.1), fun _ => 0⟩

/-- Project the segment extractor's output to the chip verifier's input. -/
def Dchip : Alg (H.Digest × IProof × CProof) (H.Digest × CProof) :=
  ⟨fun t => (t.1, t.2.2), fun _ => 0⟩

theorem isPoly_Dstep :
    IsPoly (Dstep : Alg (H.Digest × IProof × CProof) (H.Digest × IProof)) where
  costPoly := ⟨0, fun a => by simp [Dstep]⟩
  sizePoly := ⟨Polynomial.X, fun a => by
    show size ((a.1, a.2.1)) ≤ Polynomial.X.eval (size a)
    rw [Polynomial.eval_X]
    show size a.1 + size a.2.1 ≤ size a.1 + (size a.2.1 + size a.2.2)
    exact Nat.add_le_add_left (Nat.le_add_right _ _) _⟩

theorem isPoly_Dchip :
    IsPoly (Dchip : Alg (H.Digest × IProof × CProof) (H.Digest × CProof)) where
  costPoly := ⟨0, fun a => by simp [Dchip]⟩
  sizePoly := ⟨Polynomial.X, fun a => by
    show size ((a.1, a.2.2)) ≤ Polynomial.X.eval (size a)
    rw [Polynomial.eval_X]
    show size a.1 + size a.2.2 ≤ size a.1 + (size a.2.1 + size a.2.2)
    exact Nat.add_le_add_left (Nat.le_add_left _ _) _⟩

/-! ## The unification glue: compare two buses, emit witness or collision -/

/-- Compare the two extracted buses. Equal ⇒ return the unified bus; different ⇒
return the pair as a collision candidate. O(1) cost. -/
def busGlue [DecidableEq H.Domain] :
    Alg (H.Domain × H.Domain) (H.Domain ⊕ (H.Domain × H.Domain)) :=
  ⟨fun bb => if bb.1 = bb.2 then Sum.inl bb.1 else Sum.inr (bb.1, bb.2), fun _ => 0⟩

theorem isPoly_busGlue [DecidableEq H.Domain] :
    IsPoly (busGlue : Alg (H.Domain × H.Domain) (H.Domain ⊕ (H.Domain × H.Domain))) where
  costPoly := ⟨0, fun a => by simp [busGlue]⟩
  sizePoly := ⟨Polynomial.X, fun a => by
    show size (if a.1 = a.2 then Sum.inl a.1 else Sum.inr (a.1, a.2)) ≤ Polynomial.X.eval (size a)
    rw [Polynomial.eval_X]
    by_cases h : a.1 = a.2
    · rw [if_pos h]
      show size a.1 ≤ size a.1 + size a.2
      exact Nat.le_add_right _ _
    · rw [if_neg h]
      show size a.1 + size a.2 ≤ size a.1 + size a.2
      exact le_refl _⟩

/-! ## The theorem -/

/-- **Efficient, unkeyed segment extraction (step + one chip).**

Given efficient (`IsPoly`), correct straight-line extractors for the segment
verifier (`Eseg`) and the two inner verifiers (`Estep`, `Echip`), plus decidable
equality on buses, there is an `IsPoly` reduction `E` that, on every accepting
proof, outputs either a valid unified bus (satisfying `stepPred` *and* `chipPred`)
or an explicit collision of `H`.

Efficiency (`IsPoly E`) is discharged purely by `IsPoly.comp`/`IsPoly.pair`;
correctness is the bus-unification argument, producing the collision in place of
assuming collision-resistance. -/
theorem segment_extract_upto_collisionE [DecidableEq H.Domain]
    (verify : Stmt → Proof → Prop)
    (istepVerify : H.Digest × IProof → Prop)
    (ichipVerify : H.Digest × CProof → Prop)
    (stepPred chipPred : H.Domain → Prop)
    (Eseg : Alg (Stmt × Proof) (H.Digest × IProof × CProof))
    (Estep : Alg (H.Digest × IProof) H.Domain)
    (Echip : Alg (H.Digest × CProof) H.Domain)
    (hEseg : IsPoly Eseg) (hEstep : IsPoly Estep) (hEchip : IsPoly Echip)
    (cseg : ∀ x p, verify x p →
        istepVerify (Dstep.run (Eseg.run (x, p))) ∧
        ichipVerify (Dchip.run (Eseg.run (x, p))))
    (cstep : ∀ s, istepVerify s → stepPred (Estep.run s) ∧ s.1 = H.hash (Estep.run s))
    (cchip : ∀ s, ichipVerify s → chipPred (Echip.run s) ∧ s.1 = H.hash (Echip.run s)) :
    ∃ E : Alg (Stmt × Proof) (H.Domain ⊕ (H.Domain × H.Domain)),
      IsPoly E ∧
      ∀ x p, verify x p →
        (∀ bus, E.run (x, p) = Sum.inl bus → stepPred bus ∧ chipPred bus) ∧
        (∀ b b', E.run (x, p) = Sum.inr (b, b') → b ≠ b' ∧ H.hash b = H.hash b') := by
  refine ⟨busGlue.comp ((Estep.comp (Dstep.comp Eseg)).pair (Echip.comp (Dchip.comp Eseg))),
      ?_, ?_⟩
  · -- Efficiency: pure composition of the parts' `IsPoly`.
    exact isPoly_busGlue.comp
      ((hEstep.comp (isPoly_Dstep.comp hEseg)).pair (hEchip.comp (isPoly_Dchip.comp hEseg)))
  · -- Correctness: the bus-unification argument, producing a collision on mismatch.
    intro x p hp
    obtain ⟨hsv, hcv⟩ := cseg x p hp
    obtain ⟨hstepPred, hstepHash⟩ := cstep _ hsv
    obtain ⟨hchipPred, hchipHash⟩ := cchip _ hcv
    -- The reduction's output, unfolded (definitionally).
    have hrun :
        (busGlue.comp
            ((Estep.comp (Dstep.comp Eseg)).pair (Echip.comp (Dchip.comp Eseg)))).run (x, p)
          = if Estep.run (Dstep.run (Eseg.run (x, p))) = Echip.run (Dchip.run (Eseg.run (x, p)))
            then Sum.inl (Estep.run (Dstep.run (Eseg.run (x, p))))
            else Sum.inr (Estep.run (Dstep.run (Eseg.run (x, p))),
                          Echip.run (Dchip.run (Eseg.run (x, p)))) := rfl
    refine ⟨?_, ?_⟩
    · -- `Sum.inl` branch: buses agree, both predicates hold on the unified bus.
      intro bus hbus
      rw [hrun] at hbus
      by_cases hbb : Estep.run (Dstep.run (Eseg.run (x, p)))
          = Echip.run (Dchip.run (Eseg.run (x, p)))
      · rw [if_pos hbb, Sum.inl.injEq] at hbus
        subst hbus
        exact ⟨hstepPred, by rw [hbb]; exact hchipPred⟩
      · rw [if_neg hbb] at hbus
        simp at hbus
    · -- `Sum.inr` branch: buses differ ⇒ explicit collision.
      intro b b' hbus
      rw [hrun] at hbus
      by_cases hbb : Estep.run (Dstep.run (Eseg.run (x, p)))
          = Echip.run (Dchip.run (Eseg.run (x, p)))
      · rw [if_pos hbb] at hbus
        simp at hbus
      · rw [if_neg hbb, Sum.inr.injEq, Prod.mk.injEq] at hbus
        obtain ⟨rfl, rfl⟩ := hbus
        exact ⟨hbb, by rw [← hstepHash, ← hchipHash]; rfl⟩

/-! ## Exact reduction costs: the naive fan-out re-runs `Eseg`

The `IsPoly` bound above is existential (`∃ p, cost ≤ p.eval size`), which hides
constants. Here we compute the reduction's cost *exactly*. It reveals that the
naive `pair`-based fan-out executes the shared segment extractor `Eseg` **twice**
— and that `Alg.share` removes exactly that redundancy. -/

@[simp] theorem Dstep_cost (t : H.Digest × IProof × CProof) :
    (Dstep : Alg (H.Digest × IProof × CProof) (H.Digest × IProof)).cost t = 0 := rfl

@[simp] theorem Dchip_cost (t : H.Digest × IProof × CProof) :
    (Dchip : Alg (H.Digest × IProof × CProof) (H.Digest × CProof)).cost t = 0 := rfl

@[simp] theorem busGlue_cost [DecidableEq H.Domain] (b : H.Domain × H.Domain) :
    (busGlue : Alg (H.Domain × H.Domain) (H.Domain ⊕ (H.Domain × H.Domain))).cost b = 0 := rfl

variable [DecidableEq H.Domain]
variable (Eseg : Alg (Stmt × Proof) (H.Digest × IProof × CProof))
  (Estep : Alg (H.Digest × IProof) H.Domain)
  (Echip : Alg (H.Digest × CProof) H.Domain)

/-- Naive reduction: fan out with `pair`, which re-runs `Eseg` in each branch. -/
def reductionPair : Alg (Stmt × Proof) (H.Domain ⊕ (H.Domain × H.Domain)) :=
  busGlue.comp ((Estep.comp (Dstep.comp Eseg)).pair (Echip.comp (Dchip.comp Eseg)))

/-- Shared reduction: run `Eseg` once, fan out with `Alg.share`. Same `run`. -/
def reductionShare : Alg (Stmt × Proof) (H.Domain ⊕ (H.Domain × H.Domain)) :=
  busGlue.comp (Alg.share Eseg (Estep.comp Dstep) (Echip.comp Dchip))

/-- **Exact cost of the naive reduction** — note the `2 *`: `Eseg` runs twice. -/
theorem reductionPair_cost (x : Stmt) (p : Proof) :
    (reductionPair Eseg Estep Echip).cost (x, p)
      = 2 * Eseg.cost (x, p)
        + Estep.cost (Dstep.run (Eseg.run (x, p)))
        + Echip.cost (Dchip.run (Eseg.run (x, p))) := by
  simp only [reductionPair, Alg.comp, Alg.pair, Function.comp,
    Dstep_cost, Dchip_cost, busGlue_cost, Nat.add_zero]
  ring

/-- **Exact cost of the shared reduction** — `Eseg` runs exactly once. -/
theorem reductionShare_cost (x : Stmt) (p : Proof) :
    (reductionShare Eseg Estep Echip).cost (x, p)
      = Eseg.cost (x, p)
        + Estep.cost (Dstep.run (Eseg.run (x, p)))
        + Echip.cost (Dchip.run (Eseg.run (x, p))) := by
  simp only [reductionShare, Alg.comp, Alg.share, Function.comp,
    Dstep_cost, Dchip_cost, busGlue_cost, Nat.add_zero, Nat.zero_add]

/-- **The redundancy, exactly:** the naive fan-out costs one extra `Eseg` run. -/
theorem reductionPair_cost_gap (x : Stmt) (p : Proof) :
    (reductionPair Eseg Estep Echip).cost (x, p)
      = (reductionShare Eseg Estep Echip).cost (x, p) + Eseg.cost (x, p) := by
  rw [reductionPair_cost, reductionShare_cost]; ring

/-- The shared reduction is still `IsPoly` — efficiency composes as before. -/
theorem isPoly_reductionShare
    (hEseg : IsPoly Eseg) (hEstep : IsPoly Estep) (hEchip : IsPoly Echip) :
    IsPoly (reductionShare Eseg Estep Echip) := by
  unfold reductionShare
  exact isPoly_busGlue.comp
    (IsPoly.share hEseg (hEstep.comp isPoly_Dstep) (hEchip.comp isPoly_Dchip))

end BusE
end VanillaZkVM
