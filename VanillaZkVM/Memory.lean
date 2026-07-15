-- This file goes at `VanillaZkVM/VanillaZkVM/Memory.lean`.

import VanillaZkVM.Crypto

/-!
# Memory extractability (Stages 0–2)

This file adds the **memory-only slice** of the whitepaper's memory-extractability
argument, following `VanillaZkVM/mem-plan.md`. It keeps the *existing*
`VectorCommitment` (no specialized memory-commitment structure) and finally
*consumes* `PositionBinding` and `PuncturedBinding`, which were declared but unused
in `Crypto.lean`.

* **Stage 0 — Model plumbing:** `FullVMState`, `Complete`, `CommitInv`.
* **Stage 1 — Concrete predicates:** the `MemStep` descriptor, the committed
  (`readC`/`writeC`) and full-memory (`readF`/`writeF`) op predicates, and the
  classified steps `stepC`/`stepF`.
* **Stage 2 — The heart:** `step_mem_extract`, the per-step lemma turning a
  committed step into a full-memory step.

In the perfect/probability-free style of `Crypto.lean`, "except with probability
`Adv`" collapses to "always", so the two binding hypotheses are consumed as plain
implications.
-/

namespace VanillaZkVM

/-! ## Stage 0 — Model plumbing -/

/-- Full VM state over the commitment's *native* index/value types: memory is the
total map `VC.Index → VC.Value`. The original `VMState = VMStateWith (Addr → Byte)`
is the instance `VC.Index := ℕ`, `VC.Value := ℕ`. No wrapper, no casts. -/
abbrev FullVMState (VC : VectorCommitment) : Type := VMStateWith (VC.Index → VC.Value)

/-- **Commitment completeness** — the one genuinely new crypto assumption: an
*honest* opening always verifies. Used to produce the honest opening that
position- and punctured-binding compare the adversarial opening against. -/
def Complete (VC : VectorCommitment) : Prop :=
  ∀ (m : VC.Index → VC.Value) (i : VC.Index),
    VC.verify (VC.commit m) i (m i) (VC.openProof m i)

/-- **Commitment invariant** linking a full state to a committed one: same `pc`
and `regs`, and the committed memory is the commitment of the full memory. Both
sides live over `VC.Index → VC.Value`, so this typechecks with no casts. -/
def CommitInv {VC : VectorCommitment} (Ŝ : CommittedVMState VC) (S : FullVMState VC) : Prop :=
  Ŝ.pc = S.pc ∧ Ŝ.regs = S.regs ∧ Ŝ.mem = VC.commit S.mem

/-- A commitment is injective on memories, given completeness and position
binding: if two memories commit to the same value they are equal. This is the
`funext` + position-binding argument shared by the read and other cases. -/
theorem mem_eq_of_commit_eq {VC : VectorCommitment}
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    {m₁ m₂ : VC.Index → VC.Value} (h : VC.commit m₁ = VC.commit m₂) : m₂ = m₁ := by
  funext i
  have h₂ : VC.verify (VC.commit m₁) i (m₂ i) (VC.openProof m₂ i) := by
    rw [h]; exact hComplete m₂ i
  exact (hpos (VC.commit m₁) i (m₁ i) (m₂ i) (VC.openProof m₁ i) (VC.openProof m₂ i)
    (hComplete m₁ i) h₂).symm

/-! ## Stage 1 — Concrete committed + full-memory predicates -/

/-- The memory-free register part of an op predicate: a relation on
`(pc₁, regs₁, pc₂, regs₂)`. Tying `addr`/`v` back to `regs 0`/`regs 1` is a side
condition living inside `regPart`, deferred to the concrete step model. -/
abbrev RegPart : Type := Word → (ℕ → Word) → Word → (ℕ → Word) → Prop

/-- The memory-step descriptor as a typed sum: read/write/other distinguished at
the type level, each carrying the opening *and* the typed address/value it feeds
to `VC.verify`. These are the "explicit witness fields" the paper demands. -/
inductive MemStep (VC : VectorCommitment) where
  | read  (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof)
  | write (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof)
  | other

variable {VC : VectorCommitment}

/-- Committed read `φ̂_read`: register part holds, memory is unchanged, and the
descriptor's opening `π` verifies `v` at `addr` under the committed memory. -/
def readC (regPart : RegPart) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof) : Prop :=
  regPart Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem ∧ VC.verify Ŝ₁.mem addr v π

/-- Committed write `φ̂_write`: register part holds, the descriptor's opening `π`
verifies the old value `vOld` at `addr` under the pre-state memory and the new
value `v` at `addr` under the post-state memory. -/
def writeC (regPart : RegPart) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof) : Prop :=
  regPart Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧
  VC.verify Ŝ₁.mem addr vOld π ∧
  VC.verify Ŝ₂.mem addr v π

/-- Full-memory read `φ_read`: register part holds, `addr` really holds `v`, and
memory is unchanged. -/
def readF (regPart : RegPart) (addr : VC.Index) (v : VC.Value)
    (S₁ S₂ : FullVMState VC) : Prop :=
  regPart S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₁.mem addr = v ∧ S₂.mem = S₁.mem

/-- Full-memory write `φ_write`: register part holds and post-memory is the
pre-memory updated at `addr` to `v` (stated point-wise to avoid a `DecidableEq`
requirement on `VC.Index`). -/
def writeF (regPart : RegPart) (addr : VC.Index) (v : VC.Value)
    (S₁ S₂ : FullVMState VC) : Prop :=
  regPart S₁.pc S₁.regs S₂.pc S₂.regs ∧
  S₂.mem addr = v ∧ (∀ j : VC.Index, j ≠ addr → S₂.mem j = S₁.mem j)

/-- Classified committed step `φ̂_step` (memory-only slice), carrying the
descriptor. Non-memory ops carry `.other` and a memory-free predicate. -/
def stepC (regPart : RegPart) (Ŝ₁ Ŝ₂ : CommittedVMState VC) : MemStep VC → Prop
  | .read addr v π => readC regPart Ŝ₁ Ŝ₂ addr v π
  | .write addr v vOld π => writeC regPart Ŝ₁ Ŝ₂ addr v vOld π
  | .other => regPart Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem

/-- Classified full-memory step `φ_step` (the real predicate), carrying the same
descriptor. The full-memory predicates ignore the opening `π`. -/
def stepF (regPart : RegPart) (S₁ S₂ : FullVMState VC) : MemStep VC → Prop
  | .read addr v _π => readF regPart addr v S₁ S₂
  | .write addr v _vOld _π => writeF regPart addr v S₁ S₂
  | .other => regPart S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem

/-! ## Stage 2 — The per-step memory-extractability lemma (the heart) -/

/-- **Memory extractability, one step.** Position-binding + punctured-binding +
completeness of `VC` lift a committed step to a full-memory step: given the
commitment invariant on both endpoints and a committed step, the corresponding
full-memory step holds for the *real* predicate.

This is the first place `PositionBinding` and `PuncturedBinding` are consumed.
The proof mirrors the paper's Step A, minus probabilities: `addr`, `v`, `vOld`,
`π` are the typed fields of the descriptor, so nothing casts. -/
theorem step_mem_extract
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hpunc : PuncturedBinding VC)
    (regPart : RegPart)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC)
    (h1 : CommitInv Ŝ₁ S₁) (h2 : CommitInv Ŝ₂ S₂)
    (hstep : stepC regPart Ŝ₁ Ŝ₂ w) :
    stepF regPart S₁ S₂ w := by
  unfold CommitInv at h1 h2
  obtain ⟨hpc1, hreg1, hmem1⟩ := h1
  obtain ⟨hpc2, hreg2, hmem2⟩ := h2
  cases w with
  | read addr v π =>
    simp only [stepC, readC] at hstep
    simp only [stepF, readF]
    obtain ⟨hreg, hmemEq, hverify⟩ := hstep
    refine ⟨?_, ?_, ?_⟩
    · rw [hpc1, hreg1, hpc2, hreg2] at hreg; exact hreg
    · -- `S₁.mem addr = v`: honest opening vs. the descriptor's `π`, via position binding.
      have hadv : VC.verify (VC.commit S₁.mem) addr v π := by rw [← hmem1]; exact hverify
      exact hpos (VC.commit S₁.mem) addr (S₁.mem addr) v (VC.openProof S₁.mem addr) π
        (hComplete S₁.mem addr) hadv
    · -- `S₂.mem = S₁.mem`: the committed memories are equal, so the memories are.
      apply mem_eq_of_commit_eq hComplete hpos
      rw [← hmem1, ← hmem2]; exact hmemEq
  | write addr v vOld π =>
    simp only [stepC, writeC] at hstep
    simp only [stepF, writeF]
    obtain ⟨hreg, hv1, hv2⟩ := hstep
    refine ⟨?_, ?_, ?_⟩
    · rw [hpc1, hreg1, hpc2, hreg2] at hreg; exact hreg
    · -- At `addr`: the new value verifies against the honest opening, via position binding.
      have hadv : VC.verify (VC.commit S₂.mem) addr v π := by rw [← hmem2]; exact hv2
      exact hpos (VC.commit S₂.mem) addr (S₂.mem addr) v (VC.openProof S₂.mem addr) π
        (hComplete S₂.mem addr) hadv
    · -- Off `addr`: the same `π` opens both commitments at `addr`, so punctured
      -- binding pins every other position.
      intro j hj
      have hC1 : VC.verify (VC.commit S₁.mem) addr vOld π := by rw [← hmem1]; exact hv1
      have hC2 : VC.verify (VC.commit S₂.mem) addr v π := by rw [← hmem2]; exact hv2
      exact (hpunc (VC.commit S₁.mem) (VC.commit S₂.mem) addr vOld v π j
        (S₁.mem j) (S₂.mem j) (VC.openProof S₁.mem j) (VC.openProof S₂.mem j)
        hC1 hC2 (hComplete S₁.mem j) (hComplete S₂.mem j) hj).symm
  | other =>
    simp only [stepC] at hstep
    simp only [stepF]
    obtain ⟨hreg, hmemEq⟩ := hstep
    refine ⟨?_, ?_⟩
    · rw [hpc1, hreg1, hpc2, hreg2] at hreg; exact hreg
    · apply mem_eq_of_commit_eq hComplete hpos
      rw [← hmem1, ← hmem2]; exact hmemEq

end VanillaZkVM
