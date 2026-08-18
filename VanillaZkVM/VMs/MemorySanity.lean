import VanillaZkVM.VMs.Memory

/-!
# Memory-binding sanity models

Both sides of the non-vacuity / separation check for the provisional binding
layer (`docs/INVARIANTS.md` I6), kept out of the definitions-only
`Preliminaries/VectorCommitment.lean` and placed beside the memory
reconstruction that consumes those notions:

* `exactVC` is a deliberately non-succinct commitment satisfying completeness,
  position binding, and update binding, witnessing that the `Memory`
  extractability hypotheses are jointly satisfiable.
* `appendBitVC` appends a verifier-ignored bit to the commitment. It satisfies
  completeness and position binding — and the away-from-address agreement
  property proved below — yet **fails** update binding. So those properties do
  not imply that an accepted commitment is an output of `commit`. This does not
  assert that update binding implies position binding: the two are independent
  requirements.
* A private counterexample to `MemoryBridge` uses that ignored bit to exhibit a
  represented full-memory state before an accepted committed-memory write, but
  no full-memory state representing the commitment after the write.

The `UpdateBindingBreak` record is defined beside `UpdateBinding` in
`Preliminaries/VectorCommitment.lean`;
`UpdateBinding.not_isUpdateBindingBreak` — proved here, since that file is
definitions only — shows that no record satisfying `IsUpdateBindingBreak` can
coexist with update binding. It is not yet an explicit reduction.
-/

namespace VanillaZkVM

/-- Update binding rules out every record satisfying `IsUpdateBindingBreak`:
the equality supplied by update binding contradicts the record's final
inequality. -/
theorem VectorCommitment.UpdateBinding.not_isUpdateBindingBreak {VC : VectorCommitment}
    (hupd : VC.UpdateBinding) (b : UpdateBindingBreak VC) :
    ¬IsUpdateBindingBreak VC b := by
  rintro ⟨hat, hoff, hpre, hpost, hne⟩
  exact hne (hupd b.preMemory b.postMemory b.index b.newValue
    b.postCommitment b.proof hat hoff hpre hpost)

namespace MemorySanity

/-! ## A scheme satisfying all three assumptions -/

/-- A transparent, non-succinct authentication-path model. The proof records the
off-address contents; verification checks the claimed leaf directly and checks
every other position against the proof. A shared proof therefore permits the
addressed leaf to change while fixing the remainder of memory. -/
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

theorem exactVC_complete : exactVC.Complete := by
  intro memory index
  exact ⟨rfl, fun _ _ => rfl⟩

theorem exactVC_positionBinding : exactVC.PositionBinding := by
  intro commitment index leftValue rightValue leftProof rightProof
    hleft hright
  exact hleft.1.symm.trans hright.1

theorem exactVC_updateBinding : exactVC.UpdateBinding := by
  intro memory updated addr value commitment' proof
    hat hoff hpre hpost
  funext index
  by_cases hindex : index = addr
  · subst index
    exact hpost.1.trans hat.symm
  · exact (hpost.2 index hindex).trans
      ((hpre.2 index hindex).symm.trans (hoff index hindex).symm)

/-- The three commitment hypotheses used by memory reconstruction are jointly
satisfied by `exactVC`. -/
theorem exactVC_bindingAssumptions :
    exactVC.Complete ∧ exactVC.PositionBinding ∧ exactVC.UpdateBinding :=
  ⟨exactVC_complete, exactVC_positionBinding, exactVC_updateBinding⟩

/-! ## A counterexample without update binding -/

/-- Append one bit to the transparent commitment and ignore it in verification.
The `commit` function always sets this bit to `false`. Verification nevertheless
accepts an otherwise identical value whose bit is `true`, even though no call to
`commit` can produce it. This is precisely the behavior update binding rules
out. -/
def appendBitVC : VectorCommitment where
  Value := Bool
  Index := Bool
  Com := (Bool → Bool) × Bool
  OpenProof := Bool → Bool
  commit := fun memory => (memory, false)
  openProof := fun memory _ => memory
  verify := fun commitment index value proof =>
    exactVC.verify commitment.1 index value proof

theorem appendBitVC_complete : appendBitVC.Complete := by
  intro memory index
  exact ⟨rfl, fun _ _ => rfl⟩

theorem appendBitVC_positionBinding : appendBitVC.PositionBinding := by
  intro commitment index leftValue rightValue leftProof rightProof
    hleft hright
  exact exactVC_positionBinding commitment.1 index leftValue rightValue
    leftProof rightProof hleft hright

/-- If one proof is accepted at `addr` under two commitments, then accepted
openings under those commitments at any different address reveal the same
value. This property still does not require either commitment to be an output
of `commit`. -/
private theorem appendBitVC_openings_agree_away_from_update :
    ∀ (commitment commitment' : appendBitVC.Com)
      (addr : appendBitVC.Index) (value value' : appendBitVC.Value)
      (sharedProof : appendBitVC.OpenProof)
      (index : appendBitVC.Index) (leftValue rightValue : appendBitVC.Value)
      (leftProof rightProof : appendBitVC.OpenProof),
      appendBitVC.verify commitment addr value sharedProof →
      appendBitVC.verify commitment' addr value' sharedProof →
      appendBitVC.verify commitment index leftValue leftProof →
      appendBitVC.verify commitment' index rightValue rightProof →
      index ≠ addr → leftValue = rightValue := by
  intro commitment commitment' addr value value' sharedProof
    index leftValue rightValue leftProof rightProof
    hshared hshared' hleft hright hne
  exact hleft.1.symm.trans
    ((hshared.2 index hne).trans
      ((hshared'.2 index hne).symm.trans hright.1))

/-! ## The separation: `appendBitVC` fails update binding -/

/-- The all-zero memory used by the sanity checks. -/
def zeroMemory : Bool → Bool := fun _ => false

/-- The memory obtained by changing address `false` from `false` to `true`. -/
def singleWriteMemory : Bool → Bool :=
  fun index => if index = false then true else false

/-- `exactVC` accepts a write that changes address `false` from `false` to
`true` with one shared authentication proof, and the two commitments differ.

Kept `private` (I5): it documents why a shared opening is not enough on its own,
but nothing outside this file consumes it. -/
private theorem exactVC_accepts_changed_write :
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

/-! ## `MemoryBridge` non-vacuity -/

private def writeMemFree : MemFreePredicate :=
  fun _ _ _ _ => True

private def writePre : FullVMState exactVC :=
  ⟨0, fun _ => 0, zeroMemory⟩

private def writePreCommitted : CommittedVMState exactVC :=
  ⟨writePre.pc, writePre.regs, exactVC.commit writePre.mem⟩

private def writePostCommitted : CommittedVMState exactVC :=
  ⟨writePre.pc, writePre.regs, exactVC.commit singleWriteMemory⟩

private def changedWrite : MemStep exactVC :=
  .write false true false zeroMemory

private theorem changedWrite_committed :
    committedStep writeMemFree writePreCommitted writePostCommitted := by
  refine ⟨changedWrite, ?_⟩
  simp [changedWrite, CommittedMemory.step, CommittedMemory.write, writeMemFree, writePreCommitted,
    writePostCommitted, writePre, exactVC, zeroMemory, singleWriteMemory]

/-- `step_reconstruct` is non-vacuous for a write that changes `false` to
`true`: all three binding assumptions hold simultaneously, the committed-memory
step accepts one shared proof, and reconstruction produces a represented
full-memory state satisfying `FullMemory.step`. All data stays private, so this
non-vacuity check adds no public API. -/
example :
    ∃ S₂ : FullVMState exactVC,
      CommitInv writePostCommitted S₂ ∧
        ∃ w : MemStep exactVC, FullMemory.step writeMemFree writePre S₂ w := by
  exact step_reconstruct exactVC_complete exactVC_positionBinding
    exactVC_updateBinding writeMemFree writePre writePreCommitted
    writePostCommitted ⟨rfl, rfl, rfl⟩ changedWrite_committed

/-- A valid update-binding failure: `(zeroMemory, true)` accepts the same opening
as `(zeroMemory, false)`, which `appendBitVC.commit` produces, but is itself not
the output of `appendBitVC.commit` for any memory. -/
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

/-! ## Counterexample to `MemoryBridge` without update binding -/

private def appendBitMemFree : MemFreePredicate :=
  fun _ _ _ _ => True

private def appendBitPre : FullVMState appendBitVC :=
  ⟨0, fun _ => 0, zeroMemory⟩

private def appendBitCommittedPre : CommittedVMState appendBitVC :=
  ⟨appendBitPre.pc, appendBitPre.regs, appendBitVC.commit appendBitPre.mem⟩

private def appendBitMalformedPost : CommittedVMState appendBitVC :=
  ⟨appendBitPre.pc, appendBitPre.regs, (zeroMemory, true)⟩

private theorem appendBitMalformedStep :
    committedStep appendBitMemFree appendBitCommittedPre appendBitMalformedPost := by
  refine ⟨.write false false false zeroMemory, ?_⟩
  simp [CommittedMemory.step, CommittedMemory.write, appendBitMemFree, appendBitCommittedPre,
    appendBitMalformedPost, appendBitPre, appendBitVC, exactVC, zeroMemory]

private theorem appendBitMalformedPost_not_representable :
    ¬∃ S₂ : FullVMState appendBitVC, CommitInv appendBitMalformedPost S₂ := by
  rintro ⟨S₂, _, _, hmem⟩
  have hbit : true = false := congrArg Prod.snd hmem
  exact Bool.noConfusion hbit

/-- Without update binding, the exact antecedent of the memory bridge can hold
while its representation conclusion is impossible. This is the executable
form of the attack that motivated `UpdateBinding`: verification accepts the
second commitment even though it is not `commit m` for any full memory `m`. -/
example :
    CommitInv appendBitCommittedPre appendBitPre ∧
    committedStep appendBitMemFree appendBitCommittedPre appendBitMalformedPost ∧
    ¬∃ S₂ : FullVMState appendBitVC, CommitInv appendBitMalformedPost S₂ :=
  ⟨⟨rfl, rfl, rfl⟩, appendBitMalformedStep,
    appendBitMalformedPost_not_representable⟩

/-- `appendBitVC` satisfies completeness and position binding, as well as the
away-from-`addr` agreement property proved by
`appendBitVC_openings_agree_away_from_update`. Nevertheless, `appendBitBreak`
violates update binding because its accepted candidate commitment is not an
output of `commit`. -/
theorem appendBitVC_not_updateBinding :
    ¬appendBitVC.UpdateBinding := by
  intro hupd
  exact hupd.not_isUpdateBindingBreak appendBitBreak appendBitBreak_wins

end MemorySanity
end VanillaZkVM
