import VanillaZkVM.Zkvm

/-!
# Memory extractability

This file is the **memory-only slice** of the whitepaper's memory-extractability
argument. It keeps the *existing* `VectorCommitment` (no specialized
memory-commitment structure) and *consumes* `PositionBinding` and
`UpdateBinding`, which were declared but unused in `Crypto.lean`.

`UpdateBinding` replaces the earlier `PuncturedBinding`: establishing the
commitment invariant across a write requires concluding a reconstructed post-root
is an actual `commit` output, which the non-equivocation binding notions cannot
give. See `update-binding.md`.

* **Model plumbing:** `FullVMState` and `CommitInv` (`Complete` and
  `mem_eq_of_commit_eq` live in `Crypto.lean`).
* **Concrete predicates:** the `MemStep` descriptor, the committed
  (`readC`/`writeC`) and full-memory (`readF`/`writeF`) op predicates, and the
  classified steps `stepC`/`stepF`.
* **Per-step extractability:** `step_mem_extract`, turning a committed step into a
  full-memory step (given the commitment invariant on both endpoints).
* **Write reconstruction:** `commit_update` and `commitInv_write`, which
  *establish* the commitment invariant across a write.

In the perfect/probability-free style of `Crypto.lean`, "except with probability
`Adv`" collapses to "always", so the two binding hypotheses are consumed as plain
implications.
-/

namespace VanillaZkVM

/-! ## Model plumbing -/

/-- Full VM state over the commitment's *native* index/value types: memory is the
total map `VC.Index → VC.Value`. The original `VMState = VMStateWith (Addr → Byte)`
is the instance `VC.Index := ℕ`, `VC.Value := ℕ`. No wrapper, no casts. -/
abbrev FullVMState (VC : VectorCommitment) : Type := VMStateWith (VC.Index → VC.Value)

/-- **Commitment invariant** linking a full state to a committed one: same `pc`
and `regs`, and the committed memory is the commitment of the full memory. Both
sides live over `VC.Index → VC.Value`, so this typechecks with no casts. -/
def CommitInv {VC : VectorCommitment} (Ŝ : CommittedVMState VC) (S : FullVMState VC) : Prop :=
  Ŝ.pc = S.pc ∧ Ŝ.regs = S.regs ∧ Ŝ.mem = VC.commit S.mem

/-! ## Concrete committed + full-memory predicates -/

/-- The memory-free part of an op predicate: a relation on the non-memory state
`(pc₁, regs₁, pc₂, regs₂)`. Tying `addr`/`v` back to `regs 0`/`regs 1` is a side
condition living inside `memFreePred`, deferred to the concrete step model. -/
abbrev MemFreePredicate : Type := Word → (ℕ → Word) → Word → (ℕ → Word) → Prop

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
def readC (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof) : Prop :=
  memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem ∧ VC.verify Ŝ₁.mem addr v π

/-- Committed write `φ̂_write`: register part holds, the descriptor's opening `π`
verifies the old value `vOld` at `addr` under the pre-state memory and the new
value `v` at `addr` under the post-state memory. -/
def writeC (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof) : Prop :=
  memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧
  VC.verify Ŝ₁.mem addr vOld π ∧
  VC.verify Ŝ₂.mem addr v π

/-- Full-memory read `φ_read`: register part holds, `addr` really holds `v`, and
memory is unchanged. -/
def readF (memFreePred : MemFreePredicate) (addr : VC.Index) (v : VC.Value)
    (S₁ S₂ : FullVMState VC) : Prop :=
  memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₁.mem addr = v ∧ S₂.mem = S₁.mem

/-- Full-memory write `φ_write`: register part holds and post-memory is the
pre-memory updated at `addr` to `v` (stated point-wise to avoid a `DecidableEq`
requirement on `VC.Index`). -/
def writeF (memFreePred : MemFreePredicate) (addr : VC.Index) (v : VC.Value)
    (S₁ S₂ : FullVMState VC) : Prop :=
  memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧
  S₂.mem addr = v ∧ (∀ j : VC.Index, j ≠ addr → S₂.mem j = S₁.mem j)

/-- Classified committed step `φ̂_step` (memory-only slice), carrying the
descriptor. Non-memory ops carry `.other` and a memory-free predicate. -/
def stepC (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC) : MemStep VC → Prop
  | .read addr v π => readC memFreePred Ŝ₁ Ŝ₂ addr v π
  | .write addr v vOld π => writeC memFreePred Ŝ₁ Ŝ₂ addr v vOld π
  | .other => memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem

/-- Classified full-memory step `φ_step` (the real predicate), carrying the same
descriptor. The full-memory predicates ignore the opening `π`. -/
def stepF (memFreePred : MemFreePredicate) (S₁ S₂ : FullVMState VC) : MemStep VC → Prop
  | .read addr v _π => readF memFreePred addr v S₁ S₂
  | .write addr v _vOld _π => writeF memFreePred addr v S₁ S₂
  | .other => memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem

/-! ## The per-step memory-extractability lemma -/

/-- **Memory extractability, one step.** Position-binding + update binding +
completeness of `VC` lift a committed step to a full-memory step: given the
commitment invariant on both endpoints and a committed step, the corresponding
full-memory step holds for the *real* predicate.

This is the first place `PositionBinding` and `UpdateBinding` are consumed. The
proof mirrors the paper's Step A, minus probabilities: `addr`, `v`, `vOld`, `π`
are the typed fields of the descriptor, so nothing casts. The write case names
the point-updated pre-memory via `classical` (there is no `DecidableEq` on the
abstract `VC.Index`). -/
theorem step_mem_extract
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hupd : UpdateBinding VC)
    (memFreePred : MemFreePredicate)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC)
    (h1 : CommitInv Ŝ₁ S₁) (h2 : CommitInv Ŝ₂ S₂)
    (hstep : stepC memFreePred Ŝ₁ Ŝ₂ w) :
    stepF memFreePred S₁ S₂ w := by
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
    classical
    -- Move the two openings onto the honest commitments.
    rw [hmem1] at hv1  -- hv1 : VC.verify (VC.commit S₁.mem) addr vOld π
    rw [hmem2] at hv2  -- hv2 : VC.verify (VC.commit S₂.mem) addr v π
    -- Position binding at `addr` on each endpoint.
    have haddr1 : S₁.mem addr = vOld :=
      hpos (VC.commit S₁.mem) addr (S₁.mem addr) vOld (VC.openProof S₁.mem addr) π
        (hComplete S₁.mem addr) hv1
    have haddr2 : S₂.mem addr = v :=
      hpos (VC.commit S₂.mem) addr (S₂.mem addr) v (VC.openProof S₂.mem addr) π
        (hComplete S₂.mem addr) hv2
    -- The shared path opens the honest pre-commitment to `S₁.mem addr`.
    have hopen1 : VC.verify (VC.commit S₁.mem) addr (S₁.mem addr) π := by
      rw [haddr1]; exact hv1
    -- Update binding pins the post-root to `commit` of the point-update of `S₁.mem`;
    -- injectivity of `commit` then identifies `S₂.mem` with that point-update.
    have key : VC.commit S₂.mem
        = VC.commit (fun k => if k = addr then v else S₁.mem k) :=
      hupd S₁.mem (fun k => if k = addr then v else S₁.mem k) addr v
        (VC.commit S₂.mem) π (if_pos rfl) (fun k hk => if_neg hk) hopen1 hv2
    have hfun : (fun k => if k = addr then v else S₁.mem k) = S₂.mem :=
      mem_eq_of_commit_eq hComplete hpos key
    refine ⟨?_, haddr2, ?_⟩
    · rw [hpc1, hreg1, hpc2, hreg2] at hreg; exact hreg
    · intro j hj
      have hj2 : S₂.mem j = (if j = addr then v else S₁.mem j) := (congrFun hfun j).symm
      rw [hj2, if_neg hj]
  | other =>
    simp only [stepC] at hstep
    simp only [stepF]
    obtain ⟨hreg, hmemEq⟩ := hstep
    refine ⟨?_, ?_⟩
    · rw [hpc1, hreg1, hpc2, hreg2] at hreg; exact hreg
    · apply mem_eq_of_commit_eq hComplete hpos
      rw [← hmem1, ← hmem2]; exact hmemEq

/-! ## The commitment invariant across a write

`step_mem_extract` consumes `CommitInv` on both endpoints; the two lemmas here
*establish* it across a write. From `CommitInv` on the pre-state and a committed
write step, the post-state whose memory is `S₁.mem` point-updated at `addr` again
satisfies `CommitInv`. This is where update binding is essential: position binding
constrains only what a root opens to, and cannot show a committed root is an
actual `commit` output. Both lemmas are constructive (no `Classical.choice`), as
the post-memory is supplied rather than reconstructed. -/

/-- **Write reconstruction, memory part.** From an honest pre-root
`VC.commit mem₁`, a shared write path `π` opening it at `addr` (to `vOld`) and
opening a post-root `Ĉ₂` at `addr` to the new value `v`, together with the
point-updated post-memory `mem₂` (`mem₂ addr = v` and `mem₂ = mem₁` off `addr`),
update binding forces `Ĉ₂ = VC.commit mem₂`. -/
theorem commit_update
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hupd : UpdateBinding VC)
    (mem₁ mem₂ : VC.Index → VC.Value) (Ĉ₂ : VC.Com)
    (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof)
    (h2addr : mem₂ addr = v) (h2off : ∀ j, j ≠ addr → mem₂ j = mem₁ j)
    (hv1 : VC.verify (VC.commit mem₁) addr vOld π)
    (hv2 : VC.verify Ĉ₂ addr v π) :
    Ĉ₂ = VC.commit mem₂ := by
  have haddr1 : mem₁ addr = vOld :=
    hpos (VC.commit mem₁) addr (mem₁ addr) vOld (VC.openProof mem₁ addr) π
      (hComplete mem₁ addr) hv1
  have hopen1 : VC.verify (VC.commit mem₁) addr (mem₁ addr) π := by rw [haddr1]; exact hv1
  exact hupd mem₁ mem₂ addr v Ĉ₂ π h2addr h2off hopen1 hv2

/-- **Write reconstruction.** Given `CommitInv` on the pre-state, a committed
write step, and the reconstructed post-state `S₂` (same `pc`/`regs` as the
committed post-state `Ŝ₂`, memory `S₁.mem` point-updated at `addr` to `v`), the
commitment invariant holds on the post-state. Update binding supplies the memory
part; the register part is carried by hypothesis. -/
theorem commitInv_write
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hupd : UpdateBinding VC)
    (memFreePred : MemFreePredicate)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof)
    (h1 : CommitInv Ŝ₁ S₁)
    (hpc : Ŝ₂.pc = S₂.pc) (hreg : Ŝ₂.regs = S₂.regs)
    (h2addr : S₂.mem addr = v) (h2off : ∀ j, j ≠ addr → S₂.mem j = S₁.mem j)
    (hstep : writeC memFreePred Ŝ₁ Ŝ₂ addr v vOld π) :
    CommitInv Ŝ₂ S₂ := by
  obtain ⟨_, _, hmem1⟩ := h1
  simp only [writeC] at hstep
  obtain ⟨_, hv1, hv2⟩ := hstep
  rw [hmem1] at hv1
  exact ⟨hpc, hreg,
    commit_update hComplete hpos hupd S₁.mem S₂.mem Ŝ₂.mem addr v vOld π h2addr h2off hv1 hv2⟩

/-! ## Folding the per-step lemmas along a committed trace

`step_mem_extract` and `commitInv_write` are single-step. `trace_mem_extract`
folds them along a whole committed trace: it reconstructs the full-memory trace
from an initial full state, carries the commitment invariant across every step,
and lifts each committed step to a full-memory step. A concrete system composes
this to strengthen a committed-trace extractability statement to full memory
(see `TwoStep.System.cte_full`). -/

open Classical in
/-- Reconstruct the full-memory post-state from the full pre-state `S`, the
committed post-state `Ŝ'` (source of `pc`/`regs`), and the step descriptor:
memory is unchanged on reads and non-memory steps, point-updated on a write. -/
noncomputable def stepReconstruct (S : FullVMState VC) (Ŝ' : CommittedVMState VC) :
    MemStep VC → FullVMState VC
  | .read _ _ _       => ⟨Ŝ'.pc, Ŝ'.regs, S.mem⟩
  | .other            => ⟨Ŝ'.pc, Ŝ'.regs, S.mem⟩
  | .write addr v _ _ => ⟨Ŝ'.pc, Ŝ'.regs, fun j => if j = addr then v else S.mem j⟩

/-- The reconstructed full-memory trace: start at `S₀`, then at step `k` apply
`stepReconstruct` with the committed trace's next state and the `k`-th descriptor. -/
noncomputable def reconstructTrace (Ŝ : ℕ → CommittedVMState VC) (w : ℕ → MemStep VC)
    (S₀ : FullVMState VC) : ℕ → FullVMState VC
  | 0       => S₀
  | (k + 1) => stepReconstruct (reconstructTrace Ŝ w S₀ k) (Ŝ (k + 1)) (w k)

/-- One fold step: across any committed step, the commitment invariant passes
from the pre-state to the reconstructed post-state. Reads/non-memory steps keep
memory (and the invariant) unchanged; writes invoke `commitInv_write`. -/
theorem commitInv_step
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hupd : UpdateBinding VC)
    (memFreePred : MemFreePredicate)
    (S : FullVMState VC) (Ŝ Ŝ' : CommittedVMState VC) (w : MemStep VC)
    (h : CommitInv Ŝ S) (hs : stepC memFreePred Ŝ Ŝ' w) :
    CommitInv Ŝ' (stepReconstruct S Ŝ' w) := by
  cases w with
  | read addr v π =>
    obtain ⟨-, -, hmem⟩ := h
    simp only [stepC, readC] at hs
    obtain ⟨-, hmemEq, -⟩ := hs
    exact ⟨rfl, rfl, by show Ŝ'.mem = VC.commit S.mem; rw [← hmemEq]; exact hmem⟩
  | other =>
    obtain ⟨-, -, hmem⟩ := h
    simp only [stepC] at hs
    obtain ⟨-, hmemEq⟩ := hs
    exact ⟨rfl, rfl, by show Ŝ'.mem = VC.commit S.mem; rw [← hmemEq]; exact hmem⟩
  | write addr v vOld π =>
    simp only [stepC] at hs
    exact commitInv_write hComplete hpos hupd memFreePred S
      (stepReconstruct S Ŝ' (.write addr v vOld π)) Ŝ Ŝ' addr v vOld π
      h rfl rfl (by simp [stepReconstruct]) (fun j hj => by simp [stepReconstruct, hj]) hs

/-- **Trace fold.** Given a committed trace `Ŝ`, its per-step descriptors `w`
(each certifying a committed step), and an initial full state `S₀` matching
`Ŝ 0` under the commitment invariant, the reconstructed full-memory trace
`reconstructTrace Ŝ w S₀` (i) satisfies the commitment invariant at every state
and (ii) realizes every committed step as a full-memory step. This is the
whole-trace form of memory extractability. -/
theorem trace_mem_extract
    (hComplete : Complete VC) (hpos : PositionBinding VC) (hupd : UpdateBinding VC)
    (memFreePred : MemFreePredicate) (T : ℕ)
    (Ŝ : ℕ → CommittedVMState VC) (w : ℕ → MemStep VC) (S₀ : FullVMState VC)
    (hseed : CommitInv (Ŝ 0) S₀)
    (hstep : ∀ k, k < T → stepC memFreePred (Ŝ k) (Ŝ (k + 1)) (w k)) :
    (∀ k, k ≤ T → CommitInv (Ŝ k) (reconstructTrace Ŝ w S₀ k)) ∧
    (∀ k, k < T → stepF memFreePred (reconstructTrace Ŝ w S₀ k)
                     (reconstructTrace Ŝ w S₀ (k + 1)) (w k)) := by
  have hinv : ∀ k, k ≤ T → CommitInv (Ŝ k) (reconstructTrace Ŝ w S₀ k) := by
    intro k
    induction k with
    | zero => intro _; exact hseed
    | succ n ih =>
      intro hn
      show CommitInv (Ŝ (n + 1))
        (stepReconstruct (reconstructTrace Ŝ w S₀ n) (Ŝ (n + 1)) (w n))
      exact commitInv_step hComplete hpos hupd memFreePred
        (reconstructTrace Ŝ w S₀ n) (Ŝ n) (Ŝ (n + 1)) (w n) (ih (by omega)) (hstep n (by omega))
  refine ⟨hinv, ?_⟩
  intro k hk
  exact step_mem_extract hComplete hpos hupd memFreePred
    (reconstructTrace Ŝ w S₀ k) (reconstructTrace Ŝ w S₀ (k + 1)) (Ŝ k) (Ŝ (k + 1)) (w k)
    (hinv k (by omega)) (hinv (k + 1) (by omega)) (hstep k hk)

open Classical in
/-- Pick a step descriptor for each transition of a committed trace: where a
committed step exists, choose a witnessing descriptor; otherwise a dummy. This
lets a caller that only knows the *existential* step relation (`∃ w, stepC …`,
the shape of an abstract `ZkVM.step`) still drive `reconstructTrace`. -/
noncomputable def chooseDescr (memFreePred : MemFreePredicate)
    (Ŝ : ℕ → CommittedVMState VC) : ℕ → MemStep VC :=
  fun k => if h : ∃ w, stepC memFreePred (Ŝ k) (Ŝ (k + 1)) w then h.choose else MemStep.other

theorem chooseDescr_spec (memFreePred : MemFreePredicate) (Ŝ : ℕ → CommittedVMState VC)
    (k : ℕ) (h : ∃ w, stepC memFreePred (Ŝ k) (Ŝ (k + 1)) w) :
    stepC memFreePred (Ŝ k) (Ŝ (k + 1)) (chooseDescr memFreePred Ŝ k) := by
  simp only [chooseDescr]; rw [dif_pos h]; exact h.choose_spec

end VanillaZkVM
