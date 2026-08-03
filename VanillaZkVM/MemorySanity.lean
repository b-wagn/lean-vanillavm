import VanillaZkVM.Crypto

/-!
# Memory-binding sanity models

Both sides of the non-vacuity / separation check for the provisional binding
layer (`docs/INVARIANTS.md` I6), kept out of the definitions-only `Crypto.lean`:

* `exactVC` is a deliberately non-succinct commitment satisfying completeness,
  position binding, and update binding — a positive model witnessing that the
  `Memory` extractability hypotheses are jointly satisfiable.
* `appendBitVC` appends a verifier-ignored bit to the commitment. It preserves
  completeness and position binding but **fails** update binding, witnessing that
  position binding does *not* imply update binding — update binding is a genuinely
  additional requirement (the formal version of the counterexample motivating the
  retirement of the old, equally insufficient punctured-binding notion).

The break scaffolding (`UpdateBindingBreak`, `IsUpdateBindingBreak`,
`UpdateBinding.not_isUpdateBindingBreak`) also lives here: it is a certified
failure *record* used to state `appendBitVC_not_updateBinding`, not the
reduction-*emitting* form (that is a later increment).
-/

namespace VanillaZkVM

/-! ## Explicit update-binding failure records -/

/-- Data certifying an update-binding failure: a shared opening `proof` opens the
honest pre-root `commit preMemory` at `index` and also opens `postCommitment` at
`index` to `newValue`, yet `postCommitment` is *not* the honest commitment of the
point-updated `postMemory`. -/
structure UpdateBindingBreak (VC : VectorCommitment) where
  preMemory : VC.Index → VC.Value
  postMemory : VC.Index → VC.Value
  index : VC.Index
  newValue : VC.Value
  postCommitment : VC.Com
  proof : VC.OpenProof

/-- The winning predicate for an update-binding failure record. -/
def IsUpdateBindingBreak (VC : VectorCommitment)
    (b : UpdateBindingBreak VC) : Prop :=
  b.postMemory b.index = b.newValue ∧
  (∀ j, j ≠ b.index → b.postMemory j = b.preMemory j) ∧
  VC.verify (VC.commit b.preMemory) b.index (b.preMemory b.index) b.proof ∧
  VC.verify b.postCommitment b.index b.newValue b.proof ∧
  b.postCommitment ≠ VC.commit b.postMemory

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

theorem appendBitVC_complete : Complete appendBitVC :=
  -- The appended bit is ignored by `verify`, so this is `exactVC`'s completeness.
  fun memory index => exactVC_complete memory index

theorem appendBitVC_positionBinding : PositionBinding appendBitVC := by
  intro commitment index leftValue rightValue leftProof rightProof
    hleft hright
  exact exactVC_positionBinding commitment.1 index leftValue rightValue
    leftProof rightProof hleft hright

/-! ## The separation: `appendBitVC` fails update binding -/

/-- The all-zero memory used by the sanity checks. -/
private def zeroMemory : Bool → Bool := fun _ => false

/-- A valid update-binding failure: `(zeroMemory, true)` accepts the same opening
as the honest root but is not any output of `appendBitVC.commit`.

File-private: the exported claim is `appendBitVC_not_updateBinding`; this record
and `appendBitBreak_wins` are the data witnessing it. -/
private def appendBitBreak : UpdateBindingBreak appendBitVC where
  preMemory := zeroMemory
  postMemory := zeroMemory
  index := false
  newValue := false
  postCommitment := (zeroMemory, true)
  proof := zeroMemory

private theorem appendBitBreak_wins :
    IsUpdateBindingBreak appendBitVC appendBitBreak := by
  refine ⟨rfl, ?_, ⟨rfl, fun _ _ => rfl⟩,
    ⟨rfl, fun _ _ => rfl⟩, ?_⟩
  · intro index _
    rfl
  · intro heq
    have hbit : true = false := congrArg Prod.snd heq
    exact Bool.noConfusion hbit

/-- **Position binding does not imply update binding.** `appendBitVC` satisfies
completeness and position binding (above) yet is not update-binding — the
certified break `appendBitBreak` wins. So update binding is a genuinely additional
requirement, not derivable from position binding; this is the non-vacuity witness
that retiring punctured binding for `UpdateBinding` demands a real property, not a
notational rename. -/
theorem appendBitVC_not_updateBinding :
    ¬UpdateBinding appendBitVC := by
  intro hupd
  exact hupd.not_isUpdateBindingBreak appendBitBreak appendBitBreak_wins

end MemorySanity
end VanillaZkVM
