import VanillaZkVM.Zkvm

/-!
# Full-memory reconstruction

This file connects a classified committed-memory step to a full-memory step.
Its primary interface is reduction-shaped:

* `reconstructStepReduction` returns a reconstructed post-state or an explicit
  position/update-binding failure record;
* `reconstructStepReduction_correct` proves every output is valid;
* `reconstructStep` assumes the two binding properties only in the final
  corollary that rules out the failure branches.

Crucially, the primary theorem assumes `CommitInv` only for the pre-state. It
constructs the post full state and proves its invariant, which is the induction
unit needed by trace reconstruction.
-/

namespace VanillaZkVM

/-- Full VM state using the vector commitment's native index and value types. -/
abbrev FullVMState (VC : VectorCommitment) : Type :=
  VMStateWith (VC.Index → VC.Value)

/-- The committed and full states have the same non-memory fields, and the
committed memory is the honest commitment of the full memory. -/
def CommitInv {VC : VectorCommitment}
    (committed : CommittedVMState VC) (full : FullVMState VC) : Prop :=
  committed.pc = full.pc ∧
  committed.regs = full.regs ∧
  committed.mem = VC.commit full.mem

/-- The memory-free part of an instruction predicate. Concrete ISA semantics
will later instantiate this with program fetch, PC, and register behavior. -/
abbrev MemFreePredicate : Type :=
  Word → (ℕ → Word) → Word → (ℕ → Word) → Prop

/-- Security-relevant memory descriptor retained for every committed step. -/
inductive MemStep (VC : VectorCommitment) where
  | read (addr : VC.Index) (value : VC.Value) (proof : VC.OpenProof)
  | write (addr : VC.Index) (value oldValue : VC.Value)
      (proof : VC.OpenProof)
  | other

variable {VC : VectorCommitment}

/-- Committed read predicate: the non-memory transition holds, memory is
unchanged, and the supplied opening verifies the read value. -/
def readC (memFreePred : MemFreePredicate)
    (pre post : CommittedVMState VC) (addr : VC.Index) (value : VC.Value)
    (proof : VC.OpenProof) : Prop :=
  memFreePred pre.pc pre.regs post.pc post.regs ∧
  pre.mem = post.mem ∧
  VC.verify pre.mem addr value proof

/-- Committed write predicate: one path opens the old root to `oldValue` and the
candidate post-root to `value`. -/
def writeC (memFreePred : MemFreePredicate)
    (pre post : CommittedVMState VC) (addr : VC.Index)
    (value oldValue : VC.Value) (proof : VC.OpenProof) : Prop :=
  memFreePred pre.pc pre.regs post.pc post.regs ∧
  VC.verify pre.mem addr oldValue proof ∧
  VC.verify post.mem addr value proof

/-- Full-memory read predicate. -/
def readF (memFreePred : MemFreePredicate)
    (addr : VC.Index) (value : VC.Value)
    (pre post : FullVMState VC) : Prop :=
  memFreePred pre.pc pre.regs post.pc post.regs ∧
  pre.mem addr = value ∧
  post.mem = pre.mem

/-- Full-memory write predicate, stated pointwise to keep the abstract
commitment interface independent of decidable index equality. -/
def writeF (memFreePred : MemFreePredicate)
    (addr : VC.Index) (value : VC.Value)
    (pre post : FullVMState VC) : Prop :=
  memFreePred pre.pc pre.regs post.pc post.regs ∧
  post.mem addr = value ∧
  ∀ j, j ≠ addr → post.mem j = pre.mem j

/-- Classified committed step. -/
def stepC (memFreePred : MemFreePredicate)
    (pre post : CommittedVMState VC) : MemStep VC → Prop
  | .read addr value proof =>
      readC memFreePred pre post addr value proof
  | .write addr value oldValue proof =>
      writeC memFreePred pre post addr value oldValue proof
  | .other =>
      memFreePred pre.pc pre.regs post.pc post.regs ∧ pre.mem = post.mem

/-- Classified full-memory step. Opening proofs disappear from the semantic
predicate after reconstruction. -/
def stepF (memFreePred : MemFreePredicate)
    (pre post : FullVMState VC) : MemStep VC → Prop
  | .read addr value _ =>
      readF memFreePred addr value pre post
  | .write addr value _ _ =>
      writeF memFreePred addr value pre post
  | .other =>
      memFreePred pre.pc pre.regs post.pc post.regs ∧ post.mem = pre.mem

/-! ## Explicit one-step reduction -/

/-- Output of the one-step memory reconstruction algorithm. Failure branches
contain concrete game-winning candidates, not opaque propositions. -/
inductive StepReconstructionOutput (VC : VectorCommitment) where
  | success (post : FullVMState VC)
  | positionBreak (candidate : PositionBindingBreak VC)
  | updateBreak (candidate : UpdateBindingBreak VC)

/-- Deterministically reconstruct one full post-state or expose the exact
commitment failure preventing reconstruction.

The function does not assume binding. It compares the descriptor's old/read
value with the known pre-memory and, for writes, compares the candidate
post-root with the honest point-update commitment. -/
def reconstructStepReduction
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (pre : FullVMState VC) (committedPost : CommittedVMState VC) :
    MemStep VC → StepReconstructionOutput VC
  | .read addr value proof =>
      if pre.mem addr = value then
        .success
          { pc := committedPost.pc
            regs := committedPost.regs
            mem := pre.mem }
      else
        .positionBreak
          { commitment := VC.commit pre.mem
            index := addr
            leftValue := pre.mem addr
            rightValue := value
            leftProof := VC.openProof pre.mem addr
            rightProof := proof }
  | .write addr value oldValue proof =>
      if pre.mem addr = oldValue then
        let updated := fun j => if j = addr then value else pre.mem j
        if committedPost.mem = VC.commit updated then
          .success
            { pc := committedPost.pc
              regs := committedPost.regs
              mem := updated }
        else
          .updateBreak
            { preMemory := pre.mem
              postMemory := updated
              index := addr
              newValue := value
              postCommitment := committedPost.mem
              proof := proof }
      else
        .positionBreak
          { commitment := VC.commit pre.mem
            index := addr
            leftValue := pre.mem addr
            rightValue := oldValue
            leftProof := VC.openProof pre.mem addr
            rightProof := proof }
  | .other =>
      .success
        { pc := committedPost.pc
          regs := committedPost.regs
          mem := pre.mem }

/-- Every output of `reconstructStepReduction` is justified: success carries
the post commitment invariant and full-step semantics; either failure branch
is a certified binding-game win.

This theorem assumes completeness to certify the honest side of a
position-binding collision, but it assumes neither binding property. -/
theorem reconstructStepReduction_correct
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (memFreePred : MemFreePredicate)
    (pre : FullVMState VC) (committedPre committedPost : CommittedVMState VC)
    (descriptor : MemStep VC)
    (hInv : CommitInv committedPre pre)
    (hStep : stepC memFreePred committedPre committedPost descriptor) :
    match reconstructStepReduction pre committedPost descriptor with
    | .success post =>
        CommitInv committedPost post ∧
        stepF memFreePred pre post descriptor
    | .positionBreak candidate =>
        IsPositionBindingBreak VC candidate
    | .updateBreak candidate =>
        IsUpdateBindingBreak VC candidate := by
  obtain ⟨hpc, hregs, hmem⟩ := hInv
  cases descriptor with
  | read addr value proof =>
      simp only [stepC, readC] at hStep
      obtain ⟨hsem, hmemEq, hverify⟩ := hStep
      have hsemFull :
          memFreePred pre.pc pre.regs committedPost.pc committedPost.regs := by
        rw [← hpc, ← hregs]
        exact hsem
      by_cases hvalue : pre.mem addr = value
      · simp only [reconstructStepReduction, hvalue, ↓reduceIte]
        refine ⟨⟨rfl, rfl, hmemEq.symm.trans hmem⟩, ?_⟩
        exact ⟨hsemFull, hvalue, rfl⟩
      · simp only [reconstructStepReduction, hvalue, ↓reduceIte]
        refine ⟨hComplete pre.mem addr, ?_, hvalue⟩
        rw [← hmem]
        exact hverify
  | write addr value oldValue proof =>
      simp only [stepC, writeC] at hStep
      obtain ⟨hsem, hverifyPre, hverifyPost⟩ := hStep
      have hsemFull :
          memFreePred pre.pc pre.regs committedPost.pc committedPost.regs := by
        rw [← hpc, ← hregs]
        exact hsem
      by_cases hold : pre.mem addr = oldValue
      · let updated := fun j => if j = addr then value else pre.mem j
        by_cases hroot : committedPost.mem = VC.commit updated
        · simp only [reconstructStepReduction, hold, ↓reduceIte, updated, hroot]
          refine ⟨⟨rfl, rfl, hroot⟩, hsemFull, if_pos rfl, ?_⟩
          intro j hj
          exact if_neg hj
        · simp only [reconstructStepReduction, hold, ↓reduceIte, updated, hroot]
          refine ⟨if_pos rfl, ?_, ?_, hverifyPost, hroot⟩
          · intro j hj
            exact if_neg hj
          · change
              VC.verify (VC.commit pre.mem) addr (pre.mem addr) proof
            rw [hold, ← hmem]
            exact hverifyPre
      · simp only [reconstructStepReduction, hold, ↓reduceIte]
        refine ⟨hComplete pre.mem addr, ?_, hold⟩
        rw [← hmem]
        exact hverifyPre
  | other =>
      simp only [stepC] at hStep
      obtain ⟨hsem, hmemEq⟩ := hStep
      have hsemFull :
          memFreePred pre.pc pre.regs committedPost.pc committedPost.regs := by
        rw [← hpc, ← hregs]
        exact hsem
      simp only [reconstructStepReduction]
      exact ⟨⟨rfl, rfl, hmemEq.symm.trans hmem⟩, hsemFull, rfl⟩

/-- Under position and update binding, the explicit reduction must take its
success branch. The returned equality exposes the exact algorithm used by the
trace fold. -/
theorem reconstructStepReduction_success
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : MemFreePredicate)
    (pre : FullVMState VC) (committedPre committedPost : CommittedVMState VC)
    (descriptor : MemStep VC)
    (hInv : CommitInv committedPre pre)
    (hStep : stepC memFreePred committedPre committedPost descriptor) :
    ∃ post,
      reconstructStepReduction pre committedPost descriptor = .success post ∧
      CommitInv committedPost post ∧
      stepF memFreePred pre post descriptor := by
  have hcorrect := reconstructStepReduction_correct
    hComplete memFreePred pre committedPre committedPost descriptor hInv hStep
  cases houtput : reconstructStepReduction pre committedPost descriptor with
  | success post =>
      rw [houtput] at hcorrect
      exact ⟨post, rfl, hcorrect.1, hcorrect.2⟩
  | positionBreak candidate =>
      rw [houtput] at hcorrect
      exact False.elim
        (hpos.not_isPositionBindingBreak candidate hcorrect)
  | updateBreak candidate =>
      rw [houtput] at hcorrect
      exact False.elim
        (hupd.not_isUpdateBindingBreak candidate hcorrect)

set_option linter.unusedDecidableInType false in
/-- **Primary one-step reconstruction theorem.** From only the pre-state
commitment invariant and a valid committed step, construct a full post-state,
prove its commitment invariant, and prove the corresponding full-memory step.
-/
theorem reconstructStep
    [DecidableEq VC.Index] [DecidableEq VC.Value] [DecidableEq VC.Com]
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : MemFreePredicate)
    (pre : FullVMState VC) (committedPre committedPost : CommittedVMState VC)
    (descriptor : MemStep VC)
    (hInv : CommitInv committedPre pre)
    (hStep : stepC memFreePred committedPre committedPost descriptor) :
    ∃ post,
      CommitInv committedPost post ∧
      stepF memFreePred pre post descriptor := by
  obtain ⟨post, _, hpostInv, hfullStep⟩ :=
    reconstructStepReduction_success hComplete hpos hupd memFreePred
      pre committedPre committedPost descriptor hInv hStep
  exact ⟨post, hpostInv, hfullStep⟩

/-! ## Supporting endpoint lemmas -/

/-- If both endpoint invariants are already known, a committed step transfers
to the corresponding full-memory step. This is useful as a secondary lemma but
is not the induction unit for trace reconstruction. -/
theorem step_mem_extract
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : MemFreePredicate)
    (pre post : FullVMState VC)
    (committedPre committedPost : CommittedVMState VC)
    (descriptor : MemStep VC)
    (hPre : CommitInv committedPre pre)
    (hPost : CommitInv committedPost post)
    (hStep : stepC memFreePred committedPre committedPost descriptor) :
    stepF memFreePred pre post descriptor := by
  unfold CommitInv at hPre hPost
  obtain ⟨hpcPre, hregsPre, hmemPre⟩ := hPre
  obtain ⟨hpcPost, hregsPost, hmemPost⟩ := hPost
  cases descriptor with
  | read addr value proof =>
      simp only [stepC, readC] at hStep
      simp only [stepF, readF]
      obtain ⟨hsem, hmemEq, hverify⟩ := hStep
      refine ⟨?_, ?_, ?_⟩
      · rw [hpcPre, hregsPre, hpcPost, hregsPost] at hsem
        exact hsem
      · have hadv :
            VC.verify (VC.commit pre.mem) addr value proof := by
          rw [← hmemPre]
          exact hverify
        exact hpos (VC.commit pre.mem) addr (pre.mem addr) value
          (VC.openProof pre.mem addr) proof
          (hComplete pre.mem addr) hadv
      · apply mem_eq_of_commit_eq hComplete hpos
        rw [← hmemPre, ← hmemPost]
        exact hmemEq
  | write addr value oldValue proof =>
      simp only [stepC, writeC] at hStep
      simp only [stepF, writeF]
      obtain ⟨hsem, hverifyPre, hverifyPost⟩ := hStep
      classical
      rw [hmemPre] at hverifyPre
      rw [hmemPost] at hverifyPost
      have haddrPre : pre.mem addr = oldValue :=
        hpos (VC.commit pre.mem) addr (pre.mem addr) oldValue
          (VC.openProof pre.mem addr) proof
          (hComplete pre.mem addr) hverifyPre
      have haddrPost : post.mem addr = value :=
        hpos (VC.commit post.mem) addr (post.mem addr) value
          (VC.openProof post.mem addr) proof
          (hComplete post.mem addr) hverifyPost
      have hopenPre :
          VC.verify (VC.commit pre.mem) addr (pre.mem addr) proof := by
        rw [haddrPre]
        exact hverifyPre
      have hcommit :
          VC.commit post.mem =
            VC.commit (fun j => if j = addr then value else pre.mem j) :=
        hupd pre.mem (fun j => if j = addr then value else pre.mem j)
          addr value (VC.commit post.mem) proof
          (if_pos rfl) (fun j hj => if_neg hj) hopenPre hverifyPost
      have hmem :
          (fun j => if j = addr then value else pre.mem j) = post.mem :=
        mem_eq_of_commit_eq hComplete hpos hcommit
      refine ⟨?_, haddrPost, ?_⟩
      · rw [hpcPre, hregsPre, hpcPost, hregsPost] at hsem
        exact hsem
      · intro j hne
        have hpoint :
            post.mem j =
              (if j = addr then value else pre.mem j) :=
          (congrFun hmem j).symm
        rw [hpoint, if_neg hne]
  | other =>
      simp only [stepC] at hStep
      simp only [stepF]
      obtain ⟨hsem, hmemEq⟩ := hStep
      refine ⟨?_, ?_⟩
      · rw [hpcPre, hregsPre, hpcPost, hregsPost] at hsem
        exact hsem
      · apply mem_eq_of_commit_eq hComplete hpos
        rw [← hmemPre, ← hmemPost]
        exact hmemEq

/-- The memory-root component of write reconstruction. -/
theorem commit_update
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC)
    (preMemory postMemory : VC.Index → VC.Value)
    (postCommitment : VC.Com) (addr : VC.Index)
    (value oldValue : VC.Value) (proof : VC.OpenProof)
    (hat : postMemory addr = value)
    (hoff : ∀ j, j ≠ addr → postMemory j = preMemory j)
    (hverifyPre :
      VC.verify (VC.commit preMemory) addr oldValue proof)
    (hverifyPost : VC.verify postCommitment addr value proof) :
    postCommitment = VC.commit postMemory := by
  have hold : preMemory addr = oldValue :=
    hpos (VC.commit preMemory) addr (preMemory addr) oldValue
      (VC.openProof preMemory addr) proof
      (hComplete preMemory addr) hverifyPre
  have hopen :
      VC.verify (VC.commit preMemory) addr (preMemory addr) proof := by
    rw [hold]
    exact hverifyPre
  exact hupd preMemory postMemory addr value postCommitment proof
    hat hoff hopen hverifyPost

/-- Establish `CommitInv` for a supplied point-updated write post-state. -/
theorem commitInv_write
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    (hupd : UpdateBinding VC) (memFreePred : MemFreePredicate)
    (pre post : FullVMState VC)
    (committedPre committedPost : CommittedVMState VC)
    (addr : VC.Index) (value oldValue : VC.Value)
    (proof : VC.OpenProof)
    (hPre : CommitInv committedPre pre)
    (hpc : committedPost.pc = post.pc)
    (hregs : committedPost.regs = post.regs)
    (hat : post.mem addr = value)
    (hoff : ∀ j, j ≠ addr → post.mem j = pre.mem j)
    (hStep :
      writeC memFreePred committedPre committedPost
        addr value oldValue proof) :
    CommitInv committedPost post := by
  obtain ⟨_, _, hmemPre⟩ := hPre
  simp only [writeC] at hStep
  obtain ⟨_, hverifyPre, hverifyPost⟩ := hStep
  rw [hmemPre] at hverifyPre
  exact ⟨hpc, hregs,
    commit_update hComplete hpos hupd pre.mem post.mem
      committedPost.mem addr value oldValue proof
      hat hoff hverifyPre hverifyPost⟩

end VanillaZkVM
