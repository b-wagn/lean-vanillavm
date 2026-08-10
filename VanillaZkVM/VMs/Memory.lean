import VanillaZkVM.VMs.State

/-!
# Memory extractability

This file is the **memory-only slice** of the whitepaper's memory-extractability
argument. It is stated over the general `VectorCommitment` — there is no bespoke
memory-commitment structure — and *consumes* `PositionBinding` and
`UpdateBinding`, the provisional binding notions in
`Preliminaries/VectorCommitment.lean`.

`UpdateBinding` supplies the write guarantee this argument needs: the commitment
after an accepted write must equal `commit` of the updated full memory. Without
it, a write could be accepted into a commitment that no full memory maps to, and
reconstruction would have no state to produce (`MemorySanity` exhibits exactly
that).

* **Commitment injectivity:** `mem_eq_of_commit_eq` — a fact about commitments,
  proved here because `Preliminaries/VectorCommitment.lean` is definitions only.
* **State representation:** `FullVMState` and `CommitInv`.
* **Concrete predicates:** the per-transition memory witness `MemStep`, plus
  `CommittedMemory.read`/`.write`/`.step` (the `φ̂` predicates over
  `CommittedVMState`, ch03) and `FullMemory.read`/`.write`/`.step` (the `φ`
  predicates over `FullVMState`, ch01). `MemStep` sits outside both namespaces
  because the same witness indexes both step predicates. `committedStep`
  existentially hides the `MemStep` value and is the binary relation exposed
  through `StepInterface.stepCommitted`.
* **Per-step extractability:** `step_mem_extract`, turning a committed-memory
  step into a full-memory step (given `CommitInv` for both endpoint states).
* **Write reconstruction:** `commit_update` and `commitInv_write`, which
  establish `CommitInv` after a write.
* **Memory bridge:** `step_reconstruct`, which constructs the represented
  full-memory state after the step required by `StepInterface.MemoryBridge`.
* **Whole-trace extractability:** `trace_mem_extract`, chaining the per-step
  lemmas by induction along a whole committed trace (with
  `stepReconstruct`/`reconstructTrace`/`chooseMemStep`).

In the perfect/probability-free style of `Preliminaries/`, "except with
probability `Adv`" collapses to "always", so the two binding hypotheses are
consumed as plain implications.

This file mentions `StepInterface` (from `Step.lean`) only in prose and
deliberately does not import it: memory reconstruction is stated over raw states
and knows nothing of SNARKs or the abstract `ZkVM`. `VMs/TwoStep/TwoStep.lean` is
where these results are packaged through that interface.

Paper: `prop:memory-extractability` (ch05 §5.2); `φ̂_read`/`φ̂_write` (ch03).
-/

namespace VanillaZkVM

/-! ## Commitment injectivity -/

/-- A commitment is injective on memories, given completeness and position
binding: if two memories commit to the same value, they are equal.

Paper: completeness instruction preceding `def:binding`; `def:binding` (ch05). -/
theorem mem_eq_of_commit_eq {VC : VectorCommitment}
    (hComplete : VC.Complete) (hpos : VC.PositionBinding)
    {m₁ m₂ : VC.Index → VC.Value} (h : VC.commit m₁ = VC.commit m₂) : m₂ = m₁ := by
  funext i
  have h₂ : VC.verify (VC.commit m₁) i (m₂ i) (VC.openProof m₂ i) := by
    rw [h]; exact hComplete m₂ i
  exact (hpos (VC.commit m₁) i (m₁ i) (m₂ i) (VC.openProof m₁ i) (VC.openProof m₂ i)
    (hComplete m₁ i) h₂).symm

/-! ## Full-memory states and their committed representation -/

/-- Full VM state over the commitment's *native* index/value types: memory is the
total map `VC.Index → VC.Value`. The original `VMState = VMStateWith (Addr → Byte)`
is the instance `VC.Index := ℕ`, `VC.Value := ℕ`. No wrapper, no casts.

Paper: VM state in ch01. -/
abbrev FullVMState (VC : VectorCommitment) : Type := VMStateWith (VC.Index → VC.Value)

/-- `CommitInv Ŝ S` says that the committed-memory state `Ŝ` represents the
full-memory state `S`. They have the same program counter and registers. Their
memory fields contain the same memory in two forms: `S.mem` is the full map,
while `Ŝ.mem` is exactly `VC.commit S.mem`.

We call this relation the commitment invariant because memory reconstruction
proves that it holds at every position in the reconstructed trace.

Paper: `rem:mem-inheritance` (ch05) — the state-representation relation carried
along the memory-reconstruction induction. -/
def CommitInv {VC : VectorCommitment} (Ŝ : CommittedVMState VC) (S : FullVMState VC) : Prop :=
  Ŝ.pc = S.pc ∧ Ŝ.regs = S.regs ∧ Ŝ.mem = VC.commit S.mem

/-! ## Concrete committed + full-memory predicates -/

/-- The memory-free part of an op predicate: a relation on the non-memory state
`(pc₁, regs₁, pc₂, regs₂)`. This memory-only interface deliberately does not
express the equations tying a `MemStep` value's `addr`/`v` to registers; the
concrete ISA layer must conjoin those equations.

Paper: `eq:phi-read-decomp` and `eq:phi-write-decomp` (ch01). -/
abbrev MemFreePredicate : Type := Word → (ℕ → Word) → Word → (ℕ → Word) → Prop

/-- The per-transition memory witness as a typed sum: read/write/other are
distinguished at the type level, each carrying the opening *and* the typed
address/value it feeds to `VC.verify`. These are the explicit memory-opening
witness fields. `MemStep` is Lean-specific packaging for data present in the
paper's per-step memory-opening witness, not a separate paper-level notion.

Paper: `prop:memory-extractability` (ch05). -/
inductive MemStep (VC : VectorCommitment) where
  | read  (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof)
  | write (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof)
  | other

variable {VC : VectorCommitment}

/-! ### Committed-memory predicates over `CommittedVMState` (`φ̂`, ch03)

Use qualified names (`CommittedMemory.step`); do not `open` this namespace. -/

namespace CommittedMemory

/-- Committed read `φ̂_read`: register part holds, memory is unchanged, and the
`MemStep.read` witness's opening `π` verifies `v` at `addr` under the committed
memory.

Paper: `eq:op-mem-comm-read` (ch03). -/
def read (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof) : Prop :=
  memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem ∧ VC.verify Ŝ₁.mem addr v π

/-- Committed write `φ̂_write`: the register part holds, and the
`MemStep.write` witness's opening `π` verifies the old value `vOld` at `addr`
under `Ŝ₁.mem` and the new value `v` at `addr` under `Ŝ₂.mem`.

Paper: `eq:op-mem-comm-write` (ch03). -/
def write (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof) : Prop :=
  memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧
  VC.verify Ŝ₁.mem addr vOld π ∧
  VC.verify Ŝ₂.mem addr v π

/-- Committed step `φ̂_step` (memory-only slice): a case split over the
operation type carried by the `MemStep` witness (the paper's disjunction over
ops). Non-memory ops carry `.other` and a memory-free predicate. It omits the
paper's bus and concrete ISA decoding; those layers later conjoin this memory
component.

Paper: memory component of `eq:step-bus2` (ch03). -/
def step (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC) : MemStep VC → Prop
  | .read addr v π => read memFreePred Ŝ₁ Ŝ₂ addr v π
  | .write addr v vOld π => write memFreePred Ŝ₁ Ŝ₂ addr v vOld π
  | .other => memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem

end CommittedMemory

/-! ### Full-memory predicates over `FullVMState` (`φ`, ch01)

Use qualified names (`FullMemory.step`); do not `open` this namespace. -/

namespace FullMemory

/-- Full-memory read `φ_read`: register part holds, `addr` really holds `v`, and
memory is unchanged. The index and value types are parameters, so this same
equation applies both to the memory types chosen by a commitment scheme and to
the plain VM memory `Addr → Byte`.

The pinned paper's `eq:phi-read-decomp` omits the explicit condition
`S₂.mem = S₁.mem`, although `eq:mem-op-read` and ch03 say that a read does not
change memory. This definition includes the condition so the intended read
semantics are complete. The pending paper-side correction is recorded in
`docs/PAPER_REVISION.md`.

Paper: `eq:mem-op-read` and `eq:phi-read-decomp` (ch01). -/
def read {Index Value : Type} (memFreePred : MemFreePredicate) (addr : Index) (v : Value)
    (S₁ S₂ : VMStateWith (Index → Value)) : Prop :=
  memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₁.mem addr = v ∧ S₂.mem = S₁.mem

/-- Full-memory write `φ_write`: the register part holds and `S₂.mem` is
`S₁.mem` updated at `addr` to `v` (stated point-wise to avoid a `DecidableEq`
requirement on the index type). As with `FullMemory.read`, this single
definition serves both commitment-specific memory types and plain VM memory.

Paper: `eq:mem-op-write` and `eq:phi-write-decomp` (ch01). -/
def write {Index Value : Type} (memFreePred : MemFreePredicate) (addr : Index) (v : Value)
    (S₁ S₂ : VMStateWith (Index → Value)) : Prop :=
  memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧
  S₂.mem addr = v ∧ (∀ j : Index, j ≠ addr → S₂.mem j = S₁.mem j)

/-- Full-memory step `φ_step`: the same case split over the `MemStep` witness as
`CommittedMemory.step`, but interpreted over states containing the complete
memory map. The full-memory predicates ignore the opening `π`. This is the
memory-only component, not yet the full ISA step predicate.

Paper: memory component of `φ_step` in ch03. -/
def step (memFreePred : MemFreePredicate) (S₁ S₂ : FullVMState VC) : MemStep VC → Prop
  | .read addr v _π => read memFreePred addr v S₁ S₂
  | .write addr v _vOld _π => write memFreePred addr v S₁ S₂
  | .other => memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem

end FullMemory

/-- The canonical binary committed-memory step. A step holds
when some `MemStep` witness, including any required opening proof, satisfies
`CommittedMemory.step`. The `MemStep` value remains available in extraction
witnesses, but is hidden from the public `StepInterface.stepCommitted` relation.

Paper: the memory component of `eq:step-bus2` and the per-step opening witness
in `prop:memory-extractability` (ch03/ch05). -/
def committedStep (memFreePred : MemFreePredicate)
    (Ŝ₁ Ŝ₂ : CommittedVMState VC) : Prop :=
  ∃ w : MemStep VC, CommittedMemory.step memFreePred Ŝ₁ Ŝ₂ w

/-! ## The per-step memory-extractability lemma -/

/-- **Memory extractability, one step.** Completeness, position binding, and
update binding lift a committed-memory step to a full-memory step. If
`CommitInv Ŝ₁ S₁`, `CommitInv Ŝ₂ S₂`, and
`CommittedMemory.step memFreePred Ŝ₁ Ŝ₂ w` hold, then
`FullMemory.step memFreePred S₁ S₂ w` holds for the same witness `w`.

This theorem checks two full-memory states already supplied by its caller. In
particular, it assumes `CommitInv Ŝ₂ S₂`; it does not construct `S₂` or prove
that relation. `step_reconstruct` below supplies the stronger form needed to
build a full-memory trace from only its initial state.

This is the first place `PositionBinding` and `UpdateBinding` are consumed. The
proof mirrors the paper's Step A, minus probabilities: `addr`, `v`, `vOld`, `π`
are the typed fields of `w : MemStep VC`, so nothing casts. The write case names
the point update of `S₁.mem` via `classical` (there is no `DecidableEq` on the
abstract `VC.Index`).

Paper: `prop:memory-extractability` (ch05), restricted to the memory-only
`CommittedMemory.step`/`FullMemory.step` interface above. -/
theorem step_mem_extract
    (hComplete : VC.Complete) (hpos : VC.PositionBinding) (hupd : VC.UpdateBinding)
    (memFreePred : MemFreePredicate)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC)
    (h1 : CommitInv Ŝ₁ S₁) (h2 : CommitInv Ŝ₂ S₂)
    (hstep : CommittedMemory.step memFreePred Ŝ₁ Ŝ₂ w) :
    FullMemory.step memFreePred S₁ S₂ w := by
  unfold CommitInv at h1 h2
  obtain ⟨hpc1, hreg1, hmem1⟩ := h1
  obtain ⟨hpc2, hreg2, hmem2⟩ := h2
  cases w with
  | read addr v π =>
    simp only [CommittedMemory.step, CommittedMemory.read] at hstep
    simp only [FullMemory.step, FullMemory.read]
    obtain ⟨hreg, hmemEq, hverify⟩ := hstep
    refine ⟨?_, ?_, ?_⟩
    · rw [hpc1, hreg1, hpc2, hreg2] at hreg; exact hreg
    · -- Compare the canonical `VC.openProof` with the `MemStep.read` proof.
      have hadv : VC.verify (VC.commit S₁.mem) addr v π := by rw [← hmem1]; exact hverify
      exact hpos (VC.commit S₁.mem) addr (S₁.mem addr) v (VC.openProof S₁.mem addr) π
        (hComplete S₁.mem addr) hadv
    · -- `S₂.mem = S₁.mem`: the committed memories are equal, so the memories are.
      apply mem_eq_of_commit_eq hComplete hpos
      rw [← hmem1, ← hmem2]; exact hmemEq
  | write addr v vOld π =>
    simp only [CommittedMemory.step, CommittedMemory.write] at hstep
    simp only [FullMemory.step, FullMemory.write]
    obtain ⟨hreg, hv1, hv2⟩ := hstep
    classical
    -- Rewrite the two openings using the commitments of `S₁.mem` and `S₂.mem`.
    rw [hmem1] at hv1  -- hv1 : VC.verify (VC.commit S₁.mem) addr vOld π
    rw [hmem2] at hv2  -- hv2 : VC.verify (VC.commit S₂.mem) addr v π
    -- Position binding at `addr` on each endpoint.
    have haddr1 : S₁.mem addr = vOld :=
      hpos (VC.commit S₁.mem) addr (S₁.mem addr) vOld (VC.openProof S₁.mem addr) π
        (hComplete S₁.mem addr) hv1
    have haddr2 : S₂.mem addr = v :=
      hpos (VC.commit S₂.mem) addr (S₂.mem addr) v (VC.openProof S₂.mem addr) π
        (hComplete S₂.mem addr) hv2
    -- The shared path opens `VC.commit S₁.mem` to `S₁.mem addr`.
    have hopen1 : VC.verify (VC.commit S₁.mem) addr (S₁.mem addr) π := by
      rw [haddr1]; exact hv1
    -- Update binding shows `Ŝ₂.mem` equals `commit` of the point update of `S₁.mem`;
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
    simp only [CommittedMemory.step] at hstep
    simp only [FullMemory.step]
    obtain ⟨hreg, hmemEq⟩ := hstep
    refine ⟨?_, ?_⟩
    · rw [hpc1, hreg1, hpc2, hreg2] at hreg; exact hreg
    · apply mem_eq_of_commit_eq hComplete hpos
      rw [← hmem1, ← hmem2]; exact hmemEq

/-! ## Preserving `CommitInv` across a write

`step_mem_extract` consumes `CommitInv` on both endpoints; the two lemmas here
establish it after a write. From `CommitInv Ŝ₁ S₁` and
`CommittedMemory.write … Ŝ₁ Ŝ₂ …`, the full-memory state whose memory is
`S₁.mem` point-updated at `addr` represents `Ŝ₂`. This is where update binding
is essential: position binding constrains only accepted values, whereas update
binding proves `Ŝ₂.mem` is the commitment of that updated memory. Both lemmas
avoid `Classical.choice` because the updated memory is supplied explicitly. -/

/-- **Write reconstruction, memory part.** Suppose the shared opening `π`
verifies `vOld` at `addr` against `VC.commit mem₁` and verifies the new value
`v` against a candidate commitment `Ĉ₂`. If `mem₂` is `mem₁` updated at
`addr` to `v`, update binding forces `Ĉ₂ = VC.commit mem₂`.

Paper: `def:binding` and `rem:mem-inheritance` (ch05). -/
private theorem commit_update
    (hComplete : VC.Complete) (hpos : VC.PositionBinding) (hupd : VC.UpdateBinding)
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

/-- **Write reconstruction.** Given `CommitInv Ŝ₁ S₁`, a
`CommittedMemory.write` from `Ŝ₁` to `Ŝ₂`, and a full state `S₂` whose
`pc`/`regs` agree with `Ŝ₂` and whose memory is `S₁.mem` updated at `addr` to
`v`, prove `CommitInv Ŝ₂ S₂`. Update binding proves the memory equality; the
other two field equalities are hypotheses.

Paper: write case of `rem:mem-inheritance` (ch05). -/
private theorem commitInv_write
    (hComplete : VC.Complete) (hpos : VC.PositionBinding) (hupd : VC.UpdateBinding)
    (memFreePred : MemFreePredicate)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof)
    (h1 : CommitInv Ŝ₁ S₁)
    (hpc : Ŝ₂.pc = S₂.pc) (hreg : Ŝ₂.regs = S₂.regs)
    (h2addr : S₂.mem addr = v) (h2off : ∀ j, j ≠ addr → S₂.mem j = S₁.mem j)
    (hstep : CommittedMemory.write memFreePred Ŝ₁ Ŝ₂ addr v vOld π) :
    CommitInv Ŝ₂ S₂ := by
  obtain ⟨_, _, hmem1⟩ := h1
  simp only [CommittedMemory.write] at hstep
  obtain ⟨_, hv1, hv2⟩ := hstep
  rw [hmem1] at hv1
  exact ⟨hpc, hreg,
    commit_update hComplete hpos hupd S₁.mem S₂.mem Ŝ₂.mem addr v vOld π h2addr h2off hv1 hv2⟩

/-! ## Chaining the per-step lemmas along a committed trace

`commitInv_step` and the reconstructed-state semantics are single-step.
`trace_mem_extract` chains them by induction along a whole committed trace: it
reconstructs the full-memory trace from an initial full state, proves
`CommitInv` at every index, and lifts each committed-memory step to a
full-memory step. A concrete system composes this to strengthen a committed-trace
extractability statement to full memory (see `TwoStep.System.cte`). -/

open Classical in
/-- Reconstruct the next full-memory state from the current full-memory state
`S`, the next committed-memory state `Ŝ'` (source of `pc`/`regs`), and a
`MemStep` witness:
memory is unchanged on reads and non-memory steps, point-updated on a write.

Paper: reconstruction in `rem:mem-inheritance` (ch05). -/
private noncomputable def stepReconstruct (S : FullVMState VC) (Ŝ' : CommittedVMState VC) :
    MemStep VC → FullVMState VC
  | .read _ _ _       => ⟨Ŝ'.pc, Ŝ'.regs, S.mem⟩
  | .other            => ⟨Ŝ'.pc, Ŝ'.regs, S.mem⟩
  | .write addr v _ _ => ⟨Ŝ'.pc, Ŝ'.regs, fun j => if j = addr then v else S.mem j⟩

/-- The reconstructed full-memory trace: start at `S₀`, then at step `k` apply
`stepReconstruct` with the committed trace's next state and the `k`-th
`MemStep` witness.

Paper: inductive reconstruction in `rem:mem-inheritance` (ch05). -/
noncomputable def reconstructTrace (Ŝ : ℕ → CommittedVMState VC) (w : ℕ → MemStep VC)
    (S₀ : FullVMState VC) : ℕ → FullVMState VC
  | 0       => S₀
  | (k + 1) => stepReconstruct (reconstructTrace Ŝ w S₀ k) (Ŝ (k + 1)) (w k)

/-- One induction step: if `CommitInv Ŝ S` holds and
`CommittedMemory.step … Ŝ Ŝ' w` is valid, then `CommitInv` relates `Ŝ'` to
`stepReconstruct S Ŝ' w`. Reads and non-memory operations preserve memory;
writes invoke `commitInv_write`.

Paper: induction step in `rem:mem-inheritance` (ch05). -/
private theorem commitInv_step
    (hComplete : VC.Complete) (hpos : VC.PositionBinding) (hupd : VC.UpdateBinding)
    (memFreePred : MemFreePredicate)
    (S : FullVMState VC) (Ŝ Ŝ' : CommittedVMState VC) (w : MemStep VC)
    (h : CommitInv Ŝ S) (hs : CommittedMemory.step memFreePred Ŝ Ŝ' w) :
    CommitInv Ŝ' (stepReconstruct S Ŝ' w) := by
  cases w with
  | read addr v π =>
    obtain ⟨-, -, hmem⟩ := h
    simp only [CommittedMemory.step, CommittedMemory.read] at hs
    obtain ⟨-, hmemEq, -⟩ := hs
    exact ⟨rfl, rfl, by show Ŝ'.mem = VC.commit S.mem; rw [← hmemEq]; exact hmem⟩
  | other =>
    obtain ⟨-, -, hmem⟩ := h
    simp only [CommittedMemory.step] at hs
    obtain ⟨-, hmemEq⟩ := hs
    exact ⟨rfl, rfl, by show Ŝ'.mem = VC.commit S.mem; rw [← hmemEq]; exact hmem⟩
  | write addr v vOld π =>
    simp only [CommittedMemory.step] at hs
    exact commitInv_write hComplete hpos hupd memFreePred S
      (stepReconstruct S Ŝ' (.write addr v vOld π)) Ŝ Ŝ' addr v vOld π
      h rfl rfl (by simp [stepReconstruct]) (fun j hj => by simp [stepReconstruct, hj]) hs

/-- The state produced by `stepReconstruct` satisfies the full-memory semantics
of the same `MemStep` witness. Binding is needed only to identify a read value;
the write memory equations hold by construction. Kept private because callers
use the packaged bridge below. -/
private theorem reconstructed_step_full
    (hComplete : VC.Complete) (hpos : VC.PositionBinding)
    (memFreePred : MemFreePredicate)
    (S : FullVMState VC) (Ŝ Ŝ' : CommittedVMState VC) (w : MemStep VC)
    (hInv : CommitInv Ŝ S) (hstep : CommittedMemory.step memFreePred Ŝ Ŝ' w) :
    FullMemory.step memFreePred S (stepReconstruct S Ŝ' w) w := by
  obtain ⟨hpc, hregs, hmem⟩ := hInv
  cases w with
  | read addr value proof =>
    simp only [CommittedMemory.step, CommittedMemory.read] at hstep
    obtain ⟨hsem, _, hopen⟩ := hstep
    simp only [stepReconstruct, FullMemory.step, FullMemory.read]
    refine ⟨?_, ?_, trivial⟩
    · rw [hpc, hregs] at hsem
      exact hsem
    · have hopen' : VC.verify (VC.commit S.mem) addr value proof := by
        rw [← hmem]
        exact hopen
      exact hpos (VC.commit S.mem) addr (S.mem addr) value
        (VC.openProof S.mem addr) proof (hComplete S.mem addr) hopen'
  | write addr value oldValue proof =>
    simp only [CommittedMemory.step, CommittedMemory.write] at hstep
    obtain ⟨hsem, _, _⟩ := hstep
    simp only [stepReconstruct, FullMemory.step, FullMemory.write]
    refine ⟨?_, by simp, ?_⟩
    · rw [hpc, hregs] at hsem
      exact hsem
    · intro j hj
      exact if_neg hj
  | other =>
    simp only [CommittedMemory.step] at hstep
    obtain ⟨hsem, _⟩ := hstep
    simp only [stepReconstruct, FullMemory.step]
    refine ⟨?_, trivial⟩
    rw [hpc, hregs] at hsem
    exact hsem

/-- **Realization of `StepInterface.MemoryBridge`.** From `CommitInv Ŝ₁ S₁`
and `committedStep … Ŝ₁ Ŝ₂`, construct a full-memory state `S₂` such that
`CommitInv Ŝ₂ S₂` and the corresponding `FullMemory.step` both hold.

Concretely, `S₂` takes its program counter and registers from `Ŝ₂`. A read or
non-memory operation keeps `S₁.mem`; a write changes only its stated address.
Update binding proves that this constructed memory commits to `Ŝ₂.mem`.

Unlike `step_mem_extract`, this theorem does not assume `CommitInv Ŝ₂ S₂`.
It proves that relation by preserving memory on reads/other operations and
point-updating memory on writes. This is the exact
existential direction required by `StepInterface.MemoryBridge`; a concrete
`ZkVM` instance packages it through that frozen interface.

Paper: inductive construction in `rem:mem-inheritance` and Step 6 of
`thm:main` (ch05). -/
theorem step_reconstruct
    (hComplete : VC.Complete) (hpos : VC.PositionBinding) (hupd : VC.UpdateBinding)
    (memFreePred : MemFreePredicate)
    (S₁ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (hInv : CommitInv Ŝ₁ S₁) (hstep : committedStep memFreePred Ŝ₁ Ŝ₂) :
    ∃ S₂ : FullVMState VC,
      CommitInv Ŝ₂ S₂ ∧ ∃ w : MemStep VC, FullMemory.step memFreePred S₁ S₂ w := by
  obtain ⟨w, hw⟩ := hstep
  let S₂ := stepReconstruct S₁ Ŝ₂ w
  have hInv₂ : CommitInv Ŝ₂ S₂ :=
    commitInv_step hComplete hpos hupd memFreePred S₁ Ŝ₁ Ŝ₂ w hInv hw
  exact ⟨S₂, hInv₂, w,
    reconstructed_step_full hComplete hpos memFreePred S₁ Ŝ₁ Ŝ₂ w hInv hw⟩

/-- **Memory extractability, whole trace.** Given a committed trace `Ŝ`, its
sequence `w : ℕ → MemStep VC` (each value certifying a committed step), and an
initial full state `S₀` satisfying `CommitInv (Ŝ 0) S₀`, the reconstructed
full-memory trace `reconstructTrace Ŝ w S₀` (i) satisfies `CommitInv` at every
state and (ii) realizes every committed-memory step as a full-memory step.

In plain terms, start from the one known full-memory state and apply
`stepReconstruct` once for each committed step. Induction proves that every
state produced this way really represents the corresponding committed state
and that every adjacent pair obeys the full-memory semantics.

Paper: `prop:memory-extractability` and `rem:mem-inheritance` (ch05), restricted
to the memory-only step interface. -/
theorem trace_mem_extract
    (hComplete : VC.Complete) (hpos : VC.PositionBinding) (hupd : VC.UpdateBinding)
    (memFreePred : MemFreePredicate) (T : ℕ)
    (Ŝ : ℕ → CommittedVMState VC) (w : ℕ → MemStep VC) (S₀ : FullVMState VC)
    (hseed : CommitInv (Ŝ 0) S₀)
    (hstep : ∀ k, k < T → CommittedMemory.step memFreePred (Ŝ k) (Ŝ (k + 1)) (w k)) :
    (∀ k, k ≤ T → CommitInv (Ŝ k) (reconstructTrace Ŝ w S₀ k)) ∧
    (∀ k, k < T → FullMemory.step memFreePred (reconstructTrace Ŝ w S₀ k)
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
  exact reconstructed_step_full hComplete hpos memFreePred
    (reconstructTrace Ŝ w S₀ k) (Ŝ k) (Ŝ (k + 1)) (w k)
    (hinv k (by omega)) (hstep k hk)

open Classical in
/-- Pick a `MemStep` witness for each transition of a committed trace: where a
committed step exists, choose its witnessing `MemStep` value; otherwise use a
dummy `.other`. This
lets a caller that only knows the *existential* step relation (`∃ w, CommittedMemory.step …`,
the shape of an abstract `ZkVM.step`) still drive `reconstructTrace`.

Paper: per-step memory-opening witnesses in `prop:memory-extractability` (ch05). -/
noncomputable def chooseMemStep (memFreePred : MemFreePredicate)
    (Ŝ : ℕ → CommittedVMState VC) : ℕ → MemStep VC :=
  fun k => if h : committedStep memFreePred (Ŝ k) (Ŝ (k + 1)) then h.choose else MemStep.other

theorem chooseMemStep_spec (memFreePred : MemFreePredicate) (Ŝ : ℕ → CommittedVMState VC)
    (k : ℕ) (h : committedStep memFreePred (Ŝ k) (Ŝ (k + 1))) :
    CommittedMemory.step memFreePred (Ŝ k) (Ŝ (k + 1)) (chooseMemStep memFreePred Ŝ k) := by
  simp only [chooseMemStep]; rw [dif_pos h]; exact h.choose_spec

end VanillaZkVM
