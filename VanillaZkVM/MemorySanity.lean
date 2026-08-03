import VanillaZkVM.Memory

/-!
# Memory-binding sanity models

Both sides of the non-vacuity / separation check for the provisional binding
layer (`docs/INVARIANTS.md` I6), kept out of the definitions-only `Crypto.lean`:

* `exactVC` is a deliberately non-succinct commitment satisfying completeness,
  position binding, and update binding — a positive model witnessing that the
  `Memory` extractability hypotheses are jointly satisfiable.
* `appendBitVC` appends a verifier-ignored bit to the commitment. It preserves
  completeness, position binding, and the retired punctured non-equivocation
  condition, but **fails** update binding. Thus the old hypotheses do not imply
  the commitment-realizability property needed by memory reconstruction. This
  does not assert that update binding implies position binding: the two are
  independent requirements.
* A private bridge-level attack uses that ignored bit to exhibit a represented
  pre-state and accepted committed write with no representable post-state.

The break scaffolding is defined beside `UpdateBinding` in `Crypto.lean`;
`UpdateBinding.not_isUpdateBindingBreak` below proves that any winning record
contradicts update binding. It is not yet a reduction-emitting construction.
-/

namespace VanillaZkVM

/-- Update binding rules out every certified update-binding break: the two
implications are dual, so a winning break contradicts `UpdateBinding` directly. -/
theorem UpdateBinding.not_isUpdateBindingBreak {VC : VectorCommitment}
    (hupd : UpdateBinding VC) (b : UpdateBindingBreak VC) :
    ¬IsUpdateBindingBreak VC b := by
  rintro ⟨hat, hoff, hpre, hpost, hne⟩
  exact hne (hupd b.preMemory b.postMemory b.index b.newValue
    b.postCommitment b.proof hat hoff hpre hpost)

namespace MemorySanity

/-! ## Positive model: a transparent exact commitment -/

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

theorem exactVC_complete : Complete exactVC := by
  intro memory index
  exact ⟨rfl, fun _ _ => rfl⟩

theorem exactVC_positionBinding : PositionBinding exactVC := by
  intro commitment index leftValue rightValue leftProof rightProof
    hleft hright
  exact hleft.1.symm.trans hright.1

theorem exactVC_updateBinding : UpdateBinding exactVC := by
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
    Complete exactVC ∧ PositionBinding exactVC ∧ UpdateBinding exactVC :=
  ⟨exactVC_complete, exactVC_positionBinding, exactVC_updateBinding⟩

/-! ## Negative model: append an ignored bit -/

/-- Append one bit to the transparent commitment and ignore it in verification.
Honest commitments always use `false`, so a `(·, true)` root opens exactly like
the honest root yet is not any honest commitment — breaking update binding. -/
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

private theorem appendBitVC_legacyPuncturedBinding :
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

/-! ## Constructive-bridge non-vacuity -/

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
  simp [changedWrite, stepC, writeC, writeMemFree, writePreCommitted,
    writePostCommitted, writePre, exactVC, zeroMemory, singleWriteMemory]

/-- The constructive one-step theorem is non-vacuous on a genuine changed
write: all three binding assumptions hold simultaneously, the committed step
accepts one shared path, and reconstruction produces a represented full
post-state satisfying `stepF`. All data stays private so this consistency floor
adds no public API. -/
example :
    ∃ S₂ : FullVMState exactVC,
      CommitInv writePostCommitted S₂ ∧
        ∃ w : MemStep exactVC, stepF writeMemFree writePre S₂ w := by
  exact step_reconstruct exactVC_complete exactVC_positionBinding
    exactVC_updateBinding writeMemFree writePre writePreCommitted
    writePostCommitted ⟨rfl, rfl, rfl⟩ changedWrite_committed

/-- A valid update-binding failure: `(zeroMemory, true)` accepts the same opening
as the honest root but is not any output of `appendBitVC.commit`. -/
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

/-! ## Bridge-level form of the append-bit attack -/

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
  simp [stepC, writeC, appendBitMemFree, appendBitCommittedPre,
    appendBitMalformedPost, appendBitPre, appendBitVC, exactVC, zeroMemory]

private theorem appendBitMalformedPost_not_representable :
    ¬∃ S₂ : FullVMState appendBitVC, CommitInv appendBitMalformedPost S₂ := by
  rintro ⟨S₂, _, _, hmem⟩
  have hbit : true = false := congrArg Prod.snd hmem
  exact Bool.noConfusion hbit

/-- Without update binding, the exact antecedent of the memory bridge can hold
while its representation conclusion is impossible. This is the executable
form of the out-of-image commitment attack that motivated `UpdateBinding`. -/
example :
    CommitInv appendBitCommittedPre appendBitPre ∧
    committedStep appendBitMemFree appendBitCommittedPre appendBitMalformedPost ∧
    ¬∃ S₂ : FullVMState appendBitVC, CommitInv appendBitMalformedPost S₂ :=
  ⟨⟨rfl, rfl, rfl⟩, appendBitMalformedStep,
    appendBitMalformedPost_not_representable⟩

/-- `appendBitVC` satisfies completeness and position binding (above), as well
as the punctured non-equivocation formula checked privately, yet is not
update-binding: the certified break `appendBitBreak` wins. Consequently, those
non-equivocation hypotheses do not establish that an accepted post-root is an
honest commitment output. -/
theorem appendBitVC_not_updateBinding :
    ¬UpdateBinding appendBitVC := by
  intro hupd
  exact hupd.not_isUpdateBindingBreak appendBitBreak appendBitBreak_wins

end MemorySanity
end VanillaZkVM
