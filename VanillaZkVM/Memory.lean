import VanillaZkVM.Zkvm

/-!
# Memory extractability

This file is the **memory-only slice** of the whitepaper's memory-extractability
argument. It keeps the *existing* `VectorCommitment` (no specialized
memory-commitment structure) and *consumes* `PositionBinding` and
`UpdateBinding`, the provisional binding notions in `Crypto.lean`.

`UpdateBinding` supersedes the earlier punctured-binding notion: establishing the
commitment invariant across a write requires concluding a reconstructed post-root
is an actual `commit` output, which non-equivocation binding notions cannot give.

* **Commitment injectivity:** `mem_eq_of_commit_eq` (kept here, not in the
  definitions-only kernel `Crypto.lean`).
* **Model plumbing:** `FullVMState` and `CommitInv`.
* **Concrete predicates:** the `MemStep` descriptor and the classified steps
  `stepC`/`stepF`, assembled from the file-private per-op constituents
  `readC`/`writeC` (committed) and `readF`/`writeF` (full memory).
* **Per-step extractability:** `step_mem_extract`, turning a committed step into a
  full-memory step (given the commitment invariant on both endpoints).
* **Write reconstruction:** the file-private `commit_update` and
  `commitInv_write`, which *establish* the commitment invariant across a write;
  `commitInv_step` is the exported form.
* **Trace fold:** `trace_mem_extract`, folding the per-step lemmas along a whole
  committed trace (with `stepReconstruct`/`reconstructTrace`/`chooseStepWitness`).

In the perfect/probability-free style of `Crypto.lean`, "except with probability
`Adv`" collapses to "always", so the two binding hypotheses are consumed as plain
implications.

## Paper anchors

The normative revision is pinned in `docs/PAPER_REVISION.md`; labels below are
those of the whitepaper's `sampleVM` sources.

| Lean | Paper |
|---|---|
| `FullVMState` | `S=(pc,regs,mem)`, `eq:op` (ch01) |
| `CommitInv` | the commitment invariant `Ŝ.mem=Commit(mem)`, `rem:mem-inheritance` (ch05) |
| `MemFreePredicate` | `φ'_op(pc₁,regs₁,pc₂,regs₂)`, `eq:phi-read-decomp`/`-write-decomp` (ch01) |
| `MemStep` | the memory-opening witness `π^mem`, `eq:op-mem-comm-read`/`-write` (ch03) |
| `readC`/`writeC` | `φ̂_read`/`φ̂_write`, `eq:op-mem-comm-read`/`eq:op-mem-comm-write` (ch03) |
| `readF`/`writeF` | `φ_read`/`φ_write`, `eq:phi-read-decomp`/`eq:phi-write-decomp` (ch01) |
| `stepC` | `φ̂_step`, `eq:step-bus2` (ch03), bus conjuncts dropped |
| `stepF` | `φ_step := ⋁_op φ_op`, `eq:step`/`eq:step-expanded` (ch03) |
| `step_mem_extract` | `prop:memory-extractability` (ch05), second conclusion |
| `commit_update`/`commitInv_write` | `prop:memory-extractability`, first conclusion (write case) |
| `commitInv_step` | inductive step of `rem:mem-inheritance` (ch05) |
| `stepReconstruct` | the memory reconstruction rule of `rem:mem-inheritance` (ch05) |
| `reconstructTrace`/`trace_mem_extract` | `thm:main` Step 6 (ch05) |

**Deliberate simplifications** (owned by later issues, not defects here):
`memFreePred` is opaque, so the paper's `addr = regs₁[0]`, value-register, fetch
(`code[pc₁]=op`, `eq:phiop`) and well-formedness (`regs₁[0] ∈ [n]`) conjuncts are
not modelled (Issue 3); `stepC` drops the chip/bus conjuncts of `eq:step-bus2`
(Issue 5); and advantages collapse to implications (Issues 6/8).
-/

namespace VanillaZkVM

/-! ## Commitment injectivity -/

/-- A commitment is injective on memories, given completeness and position
binding: if two memories commit to the same value, they are equal. (The `funext`
+ position-binding argument used throughout memory extraction.)

Paper: not a separately stated item — the consequence of the position-binding
clause of `def:binding` (ch05) that Step A of `prop:memory-extractability` uses
to identify a reconstructed memory with the committed one. -/
theorem mem_eq_of_commit_eq {VC : VectorCommitment}
    (hComplete : Complete VC) (hpos : PositionBinding VC)
    {m₁ m₂ : VC.Index → VC.Value} (h : VC.commit m₁ = VC.commit m₂) : m₂ = m₁ := by
  funext i
  have h₂ : VC.verify (VC.commit m₁) i (m₂ i) (VC.openProof m₂ i) := by
    rw [h]; exact hComplete m₂ i
  exact (hpos (VC.commit m₁) i (m₁ i) (m₂ i) (VC.openProof m₁ i) (VC.openProof m₂ i)
    (hComplete m₁ i) h₂).symm

/-! ## Model plumbing -/

/-- Full VM state over the commitment's *native* index/value types: memory is the
total map `VC.Index → VC.Value`. The original `VMState = VMStateWith (Addr → Byte)`
is the instance `VC.Index := ℕ`, `VC.Value := ℕ`. No wrapper, no casts.

Paper: the full-memory state `S=(pc,regs,mem)` of `eq:op` (ch01), as opposed to
the committed `Ŝ=(pc,regs,mem̂)` of ch03. -/
abbrev FullVMState (VC : VectorCommitment) : Type := VMStateWith (VC.Index → VC.Value)

/-- **Commitment invariant** linking a full state to a committed one: same `pc`
and `regs`, and the committed memory is the commitment of the full memory. Both
sides live over `VC.Index → VC.Value`, so this typechecks with no casts.

Paper: `Ŝ_k.mem = Commit(mem_k)`, the invariant carried along the induction in
`rem:mem-inheritance` and delivered as the first conclusion of
`prop:memory-extractability` (ch05). -/
def CommitInv {VC : VectorCommitment} (Ŝ : CommittedVMState VC) (S : FullVMState VC) : Prop :=
  Ŝ.pc = S.pc ∧ Ŝ.regs = S.regs ∧ Ŝ.mem = VC.commit S.mem

/-! ## Concrete committed + full-memory predicates -/

/-- The memory-free part of an op predicate: a relation on the non-memory state
`(pc₁, regs₁, pc₂, regs₂)`. Tying `addr`/`v` back to `regs 0`/`regs 1` is a side
condition living inside `memFreePred`, deferred to the concrete step model.

Paper: `φ'_op(pc₁,regs₁,pc₂,regs₂)` of `eq:phi-read-decomp`/`eq:phi-write-decomp`
(ch01), which the paper keeps literally unchanged when memory is replaced by its
commitment. The paper's `φ'_read`/`φ'_write` additionally carry the fetch
conjunct `code[pc₁]=op` (`eq:phiop`) and the well-formedness conjunct
`regs₁[0] ∈ [n]`; both are absorbed into this opaque parameter until Issue 3. -/
abbrev MemFreePredicate : Type := Word → (ℕ → Word) → Word → (ℕ → Word) → Prop

/-- The memory-step witness as a typed sum: read/write/other distinguished at
the type level, each carrying the opening *and* the typed address/value it feeds
to `VC.verify`. These are the "explicit witness fields" the paper demands.

Paper: the memory-opening witness `π^mem` — `π` for a read, `(π_write, v_old)` for
a write, unconstrained otherwise — passed as an explicit argument to
`eq:op-mem-comm-read`/`eq:op-mem-comm-write` (ch03) rather than existentially
quantified, and case-split exactly this way in the fourth hypothesis of
`prop:memory-extractability` (ch05). -/
inductive MemStep (VC : VectorCommitment) where
  | read  (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof)
  | write (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof)
  | other

variable {VC : VectorCommitment}

/-- Committed read `φ̂_read`: register part holds, memory is unchanged, and the
step witness's opening `π` verifies `v` at `addr` under the committed memory.

A constituent of `stepC`, which is the exported predicate.

Paper: `eq:op-mem-comm-read` (ch03). The paper fixes `addr := Ŝ₁.regs[0]` and
`v := Ŝ₂.regs[1]`; here both come from the step witness, the tie-back living in
`memFreePred` (Issue 3). -/
private def readC (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v : VC.Value) (π : VC.OpenProof) : Prop :=
  memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem ∧ VC.verify Ŝ₁.mem addr v π

/-- Committed write `φ̂_write`: register part holds, the step witness's opening `π`
verifies the old value `vOld` at `addr` under the pre-state memory and the new
value `v` at `addr` under the post-state memory.

A constituent of `stepC`, which is the exported predicate.

Paper: `eq:op-mem-comm-write` (ch03), whose `π^mem = (π_write, v_old)` bundles
exactly the shared authentication path and the old value used here. The paper
fixes `addr := Ŝ₁.regs[0]` and `v := Ŝ₁.regs[1]`. Sharing one `π` across the two
`Verify` calls is the paper's Merkle sibling-path structure, and is what
`UpdateBinding` is stated over. -/
private def writeC (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC)
    (addr : VC.Index) (v vOld : VC.Value) (π : VC.OpenProof) : Prop :=
  memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧
  VC.verify Ŝ₁.mem addr vOld π ∧
  VC.verify Ŝ₂.mem addr v π

/-- Full-memory read `φ_read`: register part holds, `addr` really holds `v`, and
memory is unchanged.

A constituent of `stepF`, which is the exported predicate.

Paper: `eq:phi-read-decomp` (ch01), i.e. `φ'_read ∧ mem₁[regs₁[0]]=regs₂[1] ∧
mem₂=mem₁`, whose semantics is `eq:mem-op-read`. The `mem₂=mem₁` conjunct is kept
explicit for the paper's stated reason: a read must not silently alter memory. -/
private def readF (memFreePred : MemFreePredicate) (addr : VC.Index) (v : VC.Value)
    (S₁ S₂ : FullVMState VC) : Prop :=
  memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₁.mem addr = v ∧ S₂.mem = S₁.mem

/-- Full-memory write `φ_write`: register part holds and post-memory is the
pre-memory updated at `addr` to `v` (stated point-wise to avoid a `DecidableEq`
requirement on `VC.Index`).

A constituent of `stepF`, which is the exported predicate.

Paper: `eq:phi-write-decomp` (ch01), i.e. `φ'_write ∧
mem₂ = mem₁[regs₁[0] ↦ regs₁[1]]`, whose semantics is `eq:mem-op-write`. The
point-wise phrasing is the same map, written without a decidable index equality. -/
private def writeF (memFreePred : MemFreePredicate) (addr : VC.Index) (v : VC.Value)
    (S₁ S₂ : FullVMState VC) : Prop :=
  memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧
  S₂.mem addr = v ∧ (∀ j : VC.Index, j ≠ addr → S₂.mem j = S₁.mem j)

/-- Multi-option committed step `φ̂_step` (memory-only slice), carrying the step
witness. Non-memory ops carry `.other` and a memory-free predicate.

Paper: `φ̂_step` of `eq:step-bus2` (ch03), restricted to its memory content. The
paper's predicate additionally conjoins the three chip predicates
`φ̂_keccak`/`φ̂_poseidon`/`φ̂_range` over the committed bus `B̂`, and its
disjunction ranges over the whole op taxonomy; both are Issue 5 / Issue 3 work.
The `.other` case reproduces the paper's observation that every non-memory op
carries the commitment equality `Ŝ₁.mem = Ŝ₂.mem` in place of `mem₂ = mem₁`. -/
def stepC (memFreePred : MemFreePredicate) (Ŝ₁ Ŝ₂ : CommittedVMState VC) : MemStep VC → Prop
  | .read addr v π => readC memFreePred Ŝ₁ Ŝ₂ addr v π
  | .write addr v vOld π => writeC memFreePred Ŝ₁ Ŝ₂ addr v vOld π
  | .other => memFreePred Ŝ₁.pc Ŝ₁.regs Ŝ₂.pc Ŝ₂.regs ∧ Ŝ₁.mem = Ŝ₂.mem

/-- Multi-option full-memory step `φ_step` (the real predicate), carrying the same
step witness. The full-memory predicates ignore the opening `π`.

Paper: `φ_step`, the disjunction `⋁_op φ_op` over the op taxonomy
(`eq:step`/`eq:step-expanded`, ch03). This is the predicate
`def:cte` demands of an extracted trace, and the one
`prop:memory-extractability` concludes. -/
def stepF (memFreePred : MemFreePredicate) (S₁ S₂ : FullVMState VC) : MemStep VC → Prop
  | .read addr v _π => readF memFreePred addr v S₁ S₂
  | .write addr v _vOld _π => writeF memFreePred addr v S₁ S₂
  | .other => memFreePred S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem

/-! ## Write reconstruction primitive

The single place update binding pins a reconstructed post-write root to an actual
`commit` output; shared by `step_mem_extract`'s write case and `commitInv_write`. -/

/-- **Write reconstruction, memory part.** From an honest pre-root
`VC.commit mem₁`, a shared write path `π` opening it at `addr` (to `vOld`) and
opening a post-root `Ĉ₂` at `addr` to the new value `v`, together with the
point-updated post-memory `mem₂` (`mem₂ addr = v` and `mem₂ = mem₁` off `addr`),
update binding forces `Ĉ₂ = VC.commit mem₂`.

Paper: the update-binding half of Step A of `prop:memory-extractability`, spelled
out in the "Write step" bullet of `rem:mem-inheritance` (ch05) — position binding
first identifies `v_old` with `mem₁[addr]`, turning `π` into an opening of the
*honest* root, after which the update-binding clause of `def:binding` forces the
post-root to be `Commit(mem₁[addr ↦ x])`.

File-private: it is the shared internal primitive behind `step_mem_extract`'s
write case and `commitInv_write`, not a result other modules consume. -/
private theorem commit_update
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

/-! ## The per-step memory-extractability lemma -/

/-- **Memory extractability, one step.** Position-binding + update binding +
completeness of `VC` lift a committed step to a full-memory step: given the
commitment invariant on both endpoints and a committed step, the corresponding
full-memory step holds for the *real* predicate.

This is the first place `PositionBinding` and `UpdateBinding` are consumed. The
proof mirrors the paper's Step A, minus probabilities: `addr`, `v`, `vOld`, `π`
are the typed fields of the step witness, so nothing casts. The write case names
the point-updated pre-memory via `classical` (there is no `DecidableEq` on the
abstract `VC.Index`).

Paper: the second conclusion of `prop:memory-extractability` (ch05),
`φ_step(S₁,S₂)=TRUE`. The paper bounds the failure probability by
`Adv^pos + Adv^upd`; in the perfect model that bound collapses to the implication
stated here, with the two reductions `D^pos`/`D^upd` deferred to Issue 6. The
paper also derives its `CommitInv` on the post-state rather than assuming it —
that direction is `commitInv_step` below. -/
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
    · -- `S₁.mem addr = v`: honest opening vs. the step witness's `π`, via position binding.
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
    -- Position binding pins the new value at `addr` on the post-state.
    have haddr2 : S₂.mem addr = v :=
      hpos (VC.commit S₂.mem) addr (S₂.mem addr) v (VC.openProof S₂.mem addr) π
        (hComplete S₂.mem addr) hv2
    -- Update binding (via `commit_update`) pins the post-root to `commit` of the
    -- point-update of `S₁.mem`; injectivity then identifies `S₂.mem` with it.
    have key : VC.commit S₂.mem
        = VC.commit (fun k => if k = addr then v else S₁.mem k) :=
      commit_update hComplete hpos hupd S₁.mem (fun k => if k = addr then v else S₁.mem k)
        (VC.commit S₂.mem) addr v vOld π (if_pos rfl) (fun k hk => if_neg hk) hv1 hv2
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

`step_mem_extract` consumes `CommitInv` on both endpoints; `commitInv_write`
*establishes* it across a write. From `CommitInv` on the pre-state and a committed
write step, the post-state whose memory is `S₁.mem` point-updated at `addr` again
satisfies `CommitInv`, via the `commit_update` primitive above. It is constructive
(no `Classical.choice`), as the post-memory is supplied rather than reconstructed. -/

/-- **Write reconstruction.** Given `CommitInv` on the pre-state, a committed
write step, and the reconstructed post-state `S₂` (same `pc`/`regs` as the
committed post-state `Ŝ₂`, memory `S₁.mem` point-updated at `addr` to `v`), the
commitment invariant holds on the post-state. Update binding supplies the memory
part; the register part is carried by hypothesis.

Paper: the first conclusion of `prop:memory-extractability` (ch05),
`Ŝ₂.mem = Commit(mem₂)`, in the write case. The hypotheses `h2addr`/`h2off` say
`S₂.mem` is the point update the reconstruction rule of `rem:mem-inheritance`
prescribes — which, as the paper notes, is what makes the invariant provable
rather than assumable.

File-private: `commitInv_step` is the exported form covering every step witness. -/
private theorem commitInv_write
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
committed post-state `Ŝ'` (source of `pc`/`regs`), and the step witness:
memory is unchanged on reads and non-memory steps, point-updated on a write.

Paper: the memory reconstruction rule of `rem:mem-inheritance` (ch05), the rule
`thm:main` Step 6 applies when it reconstructs the full-memory trace. The paper
selects the write branch by `code[Ŝ₁.pc]=write` and takes the address and value
from `Ŝ₁.regs[0]`/`Ŝ₁.regs[1]`; here the branch and its data come from the step
witness instead (Issue 3 supplies the tie-back). -/
noncomputable def stepReconstruct (S : FullVMState VC) (Ŝ' : CommittedVMState VC) :
    MemStep VC → FullVMState VC
  | .read _ _ _       => ⟨Ŝ'.pc, Ŝ'.regs, S.mem⟩
  | .other            => ⟨Ŝ'.pc, Ŝ'.regs, S.mem⟩
  | .write addr v _ _ => ⟨Ŝ'.pc, Ŝ'.regs, fun j => if j = addr then v else S.mem j⟩

/-- The reconstructed full-memory trace: start at `S₀`, then at step `k` apply
`stepReconstruct` with the committed trace's next state and the `k`-th step witness.

Paper: the inductive reconstruction of `thm:main` Step 6 (ch05) — `mem₀` is read
off the initial state and `mem_{k+1}` is obtained from `mem_k` by the rule stated
in `rem:mem-inheritance`. -/
noncomputable def reconstructTrace (Ŝ : ℕ → CommittedVMState VC) (w : ℕ → MemStep VC)
    (S₀ : FullVMState VC) : ℕ → FullVMState VC
  | 0       => S₀
  | (k + 1) => stepReconstruct (reconstructTrace Ŝ w S₀ k) (Ŝ (k + 1)) (w k)

/-- One fold step: across any committed step, the commitment invariant passes
from the pre-state to the reconstructed post-state. Reads/non-memory steps keep
memory (and the invariant) unchanged; writes invoke `commitInv_write`.

Paper: the inductive step of `rem:mem-inheritance` (ch05), split exactly as the
remark splits it — the write case is the only one that spends update binding,
while "all other steps" inherit the invariant from `Ŝ_{k+1}.mem = Ŝ_k.mem` with
no cryptographic assumption at all. -/
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

/-- **Trace fold.** Given a committed trace `Ŝ`, its per-step witnesses `w`
(each certifying a committed step), and an initial full state `S₀` matching
`Ŝ 0` under the commitment invariant, the reconstructed full-memory trace
`reconstructTrace Ŝ w S₀` (i) satisfies the commitment invariant at every state
and (ii) realizes every committed step as a full-memory step. This is the
whole-trace form of memory extractability.

Paper: `thm:main` Step 6 (ch05), where `prop:memory-extractability` is invoked
once per step and its two conclusions are used respectively as the induction
hypothesis for the next step (here: (i)) and as the per-step obligation of
`def:cte` (here: (ii)). The paper pays `T` times the per-step advantage; the
perfect model makes the fold free. -/
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
/-- Pick a step witness for each transition of a committed trace: where a
committed step exists, choose a witness certifying it; otherwise a dummy. This
lets a caller that only knows the *existential* step relation (`∃ w, stepC …`,
the shape of an abstract `ZkVM.step`) still drive `reconstructTrace`.

Lean-only bridge with no paper counterpart, and a deliberate deviation: ch03
supplies `π^mem` as a fixed field of the extracted `R_{0,step}` witness vector,
and ch05 states explicitly that the `φ̂_step` shorthand is *not* an existential
quantification over it. The abstract `ZkVM.step` is binary, so the witness is
projected away and recovered here by choice. Sound because any certifying witness
yields the same conclusions, but the paper's tighter reading — extractor-supplied
witnesses threaded through — is what `SegWitness.steps` retains. -/
noncomputable def chooseStepWitness (memFreePred : MemFreePredicate)
    (Ŝ : ℕ → CommittedVMState VC) : ℕ → MemStep VC :=
  fun k => if h : ∃ w, stepC memFreePred (Ŝ k) (Ŝ (k + 1)) w then h.choose else MemStep.other

theorem chooseStepWitness_spec (memFreePred : MemFreePredicate) (Ŝ : ℕ → CommittedVMState VC)
    (k : ℕ) (h : ∃ w, stepC memFreePred (Ŝ k) (Ŝ (k + 1)) w) :
    stepC memFreePred (Ŝ k) (Ŝ (k + 1)) (chooseStepWitness memFreePred Ŝ k) := by
  simp only [chooseStepWitness]; rw [dif_pos h]; exact h.choose_spec

end VanillaZkVM
