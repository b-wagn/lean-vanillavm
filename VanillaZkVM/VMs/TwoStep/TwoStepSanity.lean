import VanillaZkVM.VMs.MemorySanity
import VanillaZkVM.VMs.TwoStep.TwoStep

/-!
# Consistency-floor model for full-memory two-step CTE

A one-segment, one-step system over `MemorySanity.exactVC` witnesses that all
hypotheses of `TwoStep.System.cte_fullMemory` are jointly satisfiable (I6). Its proof
objects are relation witnesses, so both argument systems are knowledge-sound by
the identity extractor. A concrete final proof is accepted, and the step is a
genuine `.other` transition rather than an everywhere-true relation.

All declarations are private; this module adds no public API.
-/

namespace VanillaZkVM
namespace TwoStepSanity

open TwoStep
open MemorySanity

private def memFree : MemFreePredicate :=
  fun _ _ _ _ => True

private def segVerify (st : SegStmt exactVC) (w : SegWitness exactVC) : Prop :=
  w.states 0 = st.Sin ∧
  w.states 1 = st.Sout ∧
  ∀ j, j < 1 → CommittedMemory.step memFree (w.states j) (w.states (j + 1)) (w.steps j)

private def finalVerify
    (st : FinalStmt exactVC) (w : FinalWitness exactVC (SegWitness exactVC)) : Prop :=
  w.boundary 0 = st.S0 ∧
  w.boundary 1 = st.ST ∧
  ∀ i, i < 1 → segVerify ⟨w.boundary i, w.boundary (i + 1)⟩ (w.proofs i)

private def system : TwoStep.System where
  VC := exactVC
  Nseg := 1
  m := 1
  memFreePred := memFree
  SegProof := SegWitness exactVC
  segVerify := segVerify
  FinalProof := FinalWitness exactVC (SegWitness exactVC)
  finalVerify := finalVerify

private theorem assumptions : system.Assumptions := by
  constructor
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [TwoStep.System.ASSeg, TwoStep.System.RSeg, system, segVerify] using hverify
  · refine ⟨⟨fun _ proof => proof⟩, ?_⟩
    intro statement proof hverify
    simpa [TwoStep.System.ASFinal, TwoStep.System.RFinal, system, finalVerify] using hverify

private def fullState : FullVMState exactVC :=
  ⟨0, fun _ => 0, zeroMemory⟩

private def committedState : CommittedVMState exactVC :=
  toCommitted fullState

private def segmentWitness : SegWitness exactVC where
  states := fun _ => committedState
  steps := fun _ => .other

private def finalWitness : FinalWitness exactVC (SegWitness exactVC) where
  boundary := fun _ => committedState
  proofs := fun _ => segmentWitness

example : system.toZkVMFullMemory.verify ⟨fullState, fullState⟩ finalWitness := by
  simp [TwoStep.System.toZkVMFullMemory, system, finalVerify, finalWitness,
    segmentWitness, segVerify, committedState, memFree, CommittedMemory.step]

example : system.toZkVMFullMemory.CTE := by
  exact system.cte_fullMemory (by simp [system]) assumptions exactVC_complete
    exactVC_positionBinding exactVC_updateBinding

end TwoStepSanity
end VanillaZkVM
