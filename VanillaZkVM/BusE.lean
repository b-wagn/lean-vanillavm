import VanillaZkVM.Crypto
import VanillaZkVM.Cost

/-!
# Unkeyed bus unification — a tight reduction with an exact, explicit cost

The security-critical bus-unification step, as an explicit straight-line reduction
whose cost is stated **exactly** (an equation with explicit constants), not
asymptotically.

* `reductionShare` is the reduction: extract the segment witness once, run the two
  inner extractors on the projected inputs, and compare the recovered buses. On a
  match it returns the unified bus; on a mismatch it returns the two buses as an
  **explicit collision** of `H` (no collision-resistance is assumed — the
  collision is produced).
* `reductionShare_correct` — the valid-or-collision guarantee.
* `reductionShare_cost` — the **exact** cost:
  `Eseg.cost + Estep.cost + Echip.cost`.
* `reductionPair_cost` / `reductionPair_cost_gap` — the naive `pair` fan-out
  instead costs `2 * Eseg.cost + …`; the gap is exactly one extra `Eseg` run,
  which `share` removes.

Representative shape: step + one delegated chip (one collision site). More chips
are more `share`/comparison terms — mechanically the same, and the exact cost gains
one `E_chip.cost` summand per chip.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

namespace VanillaZkVM
namespace BusE

variable {H : HashCommitment}
variable {Stmt Proof IProof CProof : Type}

/-! ## O(1) data-plumbing between stages (cost 0) -/

/-- Project the segment extractor's output to the inner-step verifier's input. -/
def Dstep : Alg (H.Digest × IProof × CProof) (H.Digest × IProof) :=
  ⟨fun t => (t.1, t.2.1), fun _ => 0⟩

/-- Project the segment extractor's output to the chip verifier's input. -/
def Dchip : Alg (H.Digest × IProof × CProof) (H.Digest × CProof) :=
  ⟨fun t => (t.1, t.2.2), fun _ => 0⟩

@[simp] theorem Dstep_cost (t : H.Digest × IProof × CProof) :
    (Dstep : Alg (H.Digest × IProof × CProof) (H.Digest × IProof)).cost t = 0 := rfl

@[simp] theorem Dchip_cost (t : H.Digest × IProof × CProof) :
    (Dchip : Alg (H.Digest × IProof × CProof) (H.Digest × CProof)).cost t = 0 := rfl

/-! ## The unification glue: compare two buses, emit witness or collision -/

/-- Compare the two extracted buses. Equal ⇒ return the unified bus; different ⇒
return the pair as a collision candidate. O(1) cost. -/
def busGlue [DecidableEq H.Domain] :
    Alg (H.Domain × H.Domain) (H.Domain ⊕ (H.Domain × H.Domain)) :=
  ⟨fun bb => if bb.1 = bb.2 then Sum.inl bb.1 else Sum.inr (bb.1, bb.2), fun _ => 0⟩

@[simp] theorem busGlue_cost [DecidableEq H.Domain] (b : H.Domain × H.Domain) :
    (busGlue : Alg (H.Domain × H.Domain) (H.Domain ⊕ (H.Domain × H.Domain))).cost b = 0 := rfl

/-! ## The two reductions (same `run`, different cost accounting) -/

variable [DecidableEq H.Domain]
variable (Eseg : Alg (Stmt × Proof) (H.Digest × IProof × CProof))
  (Estep : Alg (H.Digest × IProof) H.Domain)
  (Echip : Alg (H.Digest × CProof) H.Domain)

/-- Naive reduction: fan out with `pair`, which re-runs `Eseg` in each branch. -/
def reductionPair : Alg (Stmt × Proof) (H.Domain ⊕ (H.Domain × H.Domain)) :=
  busGlue.comp ((Estep.comp (Dstep.comp Eseg)).pair (Echip.comp (Dchip.comp Eseg)))

/-- Tight reduction: run `Eseg` once, fan out with `Alg.share`. Same `run` as
`reductionPair`, but `Eseg` is charged only once. -/
def reductionShare : Alg (Stmt × Proof) (H.Domain ⊕ (H.Domain × H.Domain)) :=
  busGlue.comp (Alg.share Eseg (Estep.comp Dstep) (Echip.comp Dchip))

/-! ## Correctness of the tight reduction -/

/-- **Correctness (valid-or-collision).** Given correct straight-line extractors
for the segment verifier and the two inner verifiers, on every accepting proof the
explicit reduction `reductionShare` returns either a valid unified bus (satisfying
`stepPred` *and* `chipPred`) or an explicit collision of `H`. No collision
resistance is assumed. -/
theorem reductionShare_correct
    (verify : Stmt → Proof → Prop)
    (istepVerify : H.Digest × IProof → Prop)
    (ichipVerify : H.Digest × CProof → Prop)
    (stepPred chipPred : H.Domain → Prop)
    (cseg : ∀ x p, verify x p →
        istepVerify (Dstep.run (Eseg.run (x, p))) ∧
        ichipVerify (Dchip.run (Eseg.run (x, p))))
    (cstep : ∀ s, istepVerify s → stepPred (Estep.run s) ∧ s.1 = H.hash (Estep.run s))
    (cchip : ∀ s, ichipVerify s → chipPred (Echip.run s) ∧ s.1 = H.hash (Echip.run s))
    (x : Stmt) (p : Proof) (hp : verify x p) :
    (∀ bus, (reductionShare Eseg Estep Echip).run (x, p) = Sum.inl bus →
        stepPred bus ∧ chipPred bus) ∧
    (∀ b b', (reductionShare Eseg Estep Echip).run (x, p) = Sum.inr (b, b') →
        b ≠ b' ∧ H.hash b = H.hash b') := by
  obtain ⟨hsv, hcv⟩ := cseg x p hp
  obtain ⟨hstepPred, hstepHash⟩ := cstep _ hsv
  obtain ⟨hchipPred, hchipHash⟩ := cchip _ hcv
  have hrun : (reductionShare Eseg Estep Echip).run (x, p)
        = if Estep.run (Dstep.run (Eseg.run (x, p))) = Echip.run (Dchip.run (Eseg.run (x, p)))
          then Sum.inl (Estep.run (Dstep.run (Eseg.run (x, p))))
          else Sum.inr (Estep.run (Dstep.run (Eseg.run (x, p))),
                        Echip.run (Dchip.run (Eseg.run (x, p)))) := rfl
  refine ⟨?_, ?_⟩
  · intro bus hbus
    rw [hrun] at hbus
    by_cases hbb : Estep.run (Dstep.run (Eseg.run (x, p)))
        = Echip.run (Dchip.run (Eseg.run (x, p)))
    · rw [if_pos hbb, Sum.inl.injEq] at hbus
      subst hbus
      exact ⟨hstepPred, by rw [hbb]; exact hchipPred⟩
    · rw [if_neg hbb] at hbus
      simp at hbus
  · intro b b' hbus
    rw [hrun] at hbus
    by_cases hbb : Estep.run (Dstep.run (Eseg.run (x, p)))
        = Echip.run (Dchip.run (Eseg.run (x, p)))
    · rw [if_pos hbb] at hbus
      simp at hbus
    · rw [if_neg hbb, Sum.inr.injEq, Prod.mk.injEq] at hbus
      obtain ⟨rfl, rfl⟩ := hbus
      exact ⟨hbb, by rw [← hstepHash, ← hchipHash]; rfl⟩

/-! ## Exact reduction costs -/

/-- **Exact cost of the naive reduction** — note the `2 *`: `Eseg` runs twice. -/
theorem reductionPair_cost (x : Stmt) (p : Proof) :
    (reductionPair Eseg Estep Echip).cost (x, p)
      = 2 * Eseg.cost (x, p)
        + Estep.cost (Dstep.run (Eseg.run (x, p)))
        + Echip.cost (Dchip.run (Eseg.run (x, p))) := by
  simp only [reductionPair, Alg.comp, Alg.pair, Function.comp,
    Dstep_cost, Dchip_cost, busGlue_cost, Nat.add_zero]
  ring

/-- **Exact cost of the tight reduction** — `Eseg` runs exactly once. -/
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

end BusE
end VanillaZkVM
