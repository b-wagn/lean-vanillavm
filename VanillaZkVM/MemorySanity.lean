import VanillaZkVM.Memory

/-!
# Memory-binding sanity models

This file gives both sides of the non-vacuity check:

* `exactVC` is a deliberately non-succinct commitment satisfying completeness,
  position binding, punctured binding, and update binding;
* `appendBitVC` appends a verifier-ignored bit to the commitment. It preserves
  completeness, position binding, and the old punctured-binding property, but
  fails update binding.

The second model is the formal version of Benedikt's counterexample.
-/

namespace VanillaZkVM
namespace MemorySanity

/-- A transparent, non-succinct authentication-path model. The proof records
the off-address contents; verification checks the claimed leaf directly and
checks every other position against the proof. A shared proof therefore permits
the addressed leaf to change while fixing the remainder of memory. -/
def exactVC : VectorCommitment where
  Value := Bool
  Index := Bool
  Com := Bool → Bool
  OpenProof := Bool → Bool
  commit := fun memory => memory
  openProof := fun memory _ => memory
  verify := fun commitment index value proof =>
    commitment index = value ∧
    ∀ j, j ≠ index → commitment j = proof j

theorem exactVC_complete : Complete exactVC := by
  intro memory index
  exact ⟨rfl, fun _ _ => rfl⟩

theorem exactVC_positionBinding : PositionBinding exactVC := by
  intro commitment index leftValue rightValue leftProof rightProof
    hleft hright
  exact hleft.1.symm.trans hright.1

theorem exactVC_puncturedBinding : PuncturedBinding exactVC := by
  intro commitment commitment' addr value value' sharedProof
    index leftValue rightValue leftProof rightProof
    hshared hshared' hleft hright hne
  exact hleft.1.symm.trans
    ((hshared.2 index hne).trans
      ((hshared'.2 index hne).symm.trans hright.1))

theorem exactVC_updateBinding : UpdateBinding exactVC := by
  intro memory updated addr value commitment' proof
    hat hoff hpre hpost
  funext index
  by_cases hindex : index = addr
  · subst index
    exact hpost.1.trans hat.symm
  · exact (hpost.2 index hindex).trans
      ((hpre.2 index hindex).symm.trans (hoff index hindex).symm)

/-- Append one bit to the transparent commitment and ignore it in
verification. Honest commitments always use `false`. -/
def appendBitVC : VectorCommitment where
  Value := Bool
  Index := Bool
  Com := (Bool → Bool) × Bool
  OpenProof := Bool → Bool
  commit := fun memory => (memory, false)
  openProof := fun memory _ => memory
  verify := fun commitment index value proof =>
    exactVC.verify commitment.1 index value proof

theorem appendBitVC_complete : Complete appendBitVC := by
  intro memory index
  exact ⟨rfl, fun _ _ => rfl⟩

theorem appendBitVC_positionBinding : PositionBinding appendBitVC := by
  intro commitment index leftValue rightValue leftProof rightProof
    hleft hright
  exact exactVC_positionBinding commitment.1 index leftValue rightValue
    leftProof rightProof hleft hright

theorem appendBitVC_puncturedBinding : PuncturedBinding appendBitVC := by
  intro commitment commitment' addr value value' sharedProof
    index leftValue rightValue leftProof rightProof
    hshared hshared' hleft hright hne
  exact exactVC_puncturedBinding commitment.1 commitment'.1
    addr value value' sharedProof index leftValue rightValue
    leftProof rightProof hshared hshared' hleft hright hne

/-- The all-zero memory used by the sanity checks. -/
def zeroMemory : Bool → Bool := fun _ => false

/-- The result of genuinely changing address `false` in `zeroMemory`. -/
def singleWriteMemory : Bool → Bool :=
  fun index => if index = false then true else false

/-- The positive model accepts a genuine changed write with one shared
authentication proof, and the pre/post commitments are distinct. -/
theorem exactVC_accepts_changed_write :
    exactVC.commit zeroMemory ≠ exactVC.commit singleWriteMemory ∧
    exactVC.verify (exactVC.commit zeroMemory) false false
      (exactVC.openProof zeroMemory false) ∧
    exactVC.verify (exactVC.commit singleWriteMemory) false true
      (exactVC.openProof zeroMemory false) := by
  constructor
  · change zeroMemory ≠ singleWriteMemory
    intro heq
    have hfalse := congrFun heq false
    simp [zeroMemory, singleWriteMemory] at hfalse
  · refine ⟨exactVC_complete zeroMemory false, ?_⟩
    change
      singleWriteMemory false = true ∧
      ∀ j, j ≠ false → singleWriteMemory j = zeroMemory j
    exact ⟨by simp [singleWriteMemory],
      fun j hj => by simp [singleWriteMemory, zeroMemory, hj]⟩

/-- A valid update-binding failure: `(zeroMemory, true)` accepts the same
opening as the honest root but is not any output of `appendBitVC.commit`. -/
def appendBitBreak : UpdateBindingBreak appendBitVC where
  preMemory := zeroMemory
  postMemory := zeroMemory
  index := false
  newValue := false
  postCommitment := (zeroMemory, true)
  proof := zeroMemory

theorem appendBitBreak_wins :
    IsUpdateBindingBreak appendBitVC appendBitBreak := by
  refine ⟨rfl, ?_, ⟨rfl, fun _ _ => rfl⟩,
    ⟨rfl, fun _ _ => rfl⟩, ?_⟩
  · intro index _
    rfl
  · intro heq
    have hbit : true = false := congrArg Prod.snd heq
    exact Bool.noConfusion hbit

theorem appendBitVC_not_updateBinding :
    ¬UpdateBinding appendBitVC := by
  intro hupd
  exact hupd.not_isUpdateBindingBreak appendBitBreak appendBitBreak_wins

end MemorySanity
end VanillaZkVM
