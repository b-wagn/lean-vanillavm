import VanillaZkVM.Specification.Cte
import VanillaZkVM.VMs.Memory
import VanillaZkVM.VMs.Step

/-!
# Multi-layer recursion → `MultiStepVM` (Issue 4)

The paper's recursion tower over an **abstract leaf** relation, replacing the flat
two-layer merge in `TwoStep`. Three recursion layers — `convert` (1-to-1),
`combine` (binary 2-to-1, self-recursive), `embed` (final cap) — compose into a
`ZkVM` instance whose CTE proof unrolls a binary tree of combine nodes.

The leaf is abstract: its relation is a segment-trace relation (committed steps
from boundary to boundary), and its SNARK is parameterized. This keeps the
recursion tower independent of the bus (Issue 5).

## Main definitions
* `RecTree` — the binary recursion-tree topology.
* `MultiStep.System` — the system parameters.
* `RLeaf` / `RConvert` / `RCombine` / `REmbed` — the layer relations.
* `toZkVM` — the `ZkVM` instance over full-memory states.

## Main results
* `combine_tree` — tree-unrolling extraction: given KS of leaf, convert, and
  combine SNARKs, any accepting convert-or-combine proof for `N` steps yields
  a valid committed trace. Proved by well-founded induction on `N`.
  Generalizes `chain_flatten` from lists to trees.
* `committedTrace_extract` — embed + tree extraction produces a committed trace.
* `cte` — CTE for `MultiStepVM`, composing the SNARK half with memory
  reconstruction.

Paper: ch04 (`R_2`, `R_3`, `R_4`, `fig:topo`), `lem:convert`/`combine`/`embed`,
`rem:wellfounded`.
-/

namespace VanillaZkVM
namespace MultiStep

/-! ## Binary recursion-tree topology -/

/-- The binary recursion tree (`fig:topo`). A `leaf` covers one segment;
a `node` merges two subtrees via `combine`. -/
inductive RecTree where
  | leaf : RecTree
  | node : RecTree → RecTree → RecTree

namespace RecTree

def steps (Nseg : ℕ) : RecTree → ℕ
  | .leaf => Nseg
  | .node l r => l.steps Nseg + r.steps Nseg

def leaves : RecTree → ℕ
  | .leaf => 1
  | .node l r => l.leaves + r.leaves

def internals : RecTree → ℕ
  | .leaf => 0
  | .node l r => 1 + l.internals + r.internals

/-- The number of internal nodes is one less than the number of leaves:
exactly `m - 1` combine applications for `m` segments. -/
theorem internals_eq_leaves_sub_one (t : RecTree) : t.internals + 1 = t.leaves := by
  induction t with
  | leaf => simp [internals, leaves]
  | node l r ihl ihr => simp [internals, leaves]; omega

theorem leaves_pos (t : RecTree) : 0 < t.leaves := by
  induction t with
  | leaf => simp [leaves]
  | node l r ihl _ => simp [leaves]; omega

theorem steps_dvd_Nseg (Nseg : ℕ) (t : RecTree) : Nseg ∣ t.steps Nseg := by
  induction t with
  | leaf => exact dvd_refl _
  | node l r ihl ihr => exact Nat.dvd_add ihl ihr

theorem steps_ge_Nseg (Nseg : ℕ) (_hN : 0 < Nseg) (t : RecTree) : t.steps Nseg ≥ Nseg := by
  induction t with
  | leaf => exact le_refl _
  | node l r ihl _ => simp [steps]; omega

/-- Each leaf covers `Nseg` steps, so the total is `leaves * Nseg`. -/
theorem leaves_mul_Nseg (Nseg : ℕ) (t : RecTree) : t.leaves * Nseg = t.steps Nseg := by
  induction t with
  | leaf => simp [leaves, steps]
  | node l r ihl ihr => simp [leaves, steps, Nat.add_mul, ihl, ihr]

end RecTree

/-! ## Data types -/

/-- Segment witness: intermediate committed states and one `MemStep` per
transition. Same shape as `TwoStep.SegWitness`. -/
structure SegWitness (VC : VectorCommitment) where
  states : ℕ → CommittedVMState VC
  steps : ℕ → MemStep VC

/-- Statement carrying committed boundary states and a step count. Used by the
leaf, convert, and combine relations. -/
structure RecStmt (VC : VectorCommitment) where
  S0 : CommittedVMState VC
  SN : CommittedVMState VC
  N : ℕ

/-- Statement for the embed layer: boundary states only (`T` is a fixed system
parameter).

Paper: `R_4` statement in ch04. -/
structure EmbedStmt (VC : VectorCommitment) where
  S0 : CommittedVMState VC
  ST : CommittedVMState VC

/-- Witness for the combine relation: left and right proofs (each from either
convert or combine), the midpoint state, and the child step counts.

Paper: `R_3` witness in ch04. -/
structure CombineWitness (VC : VectorCommitment) (ConvertProof CombineProof : Type) where
  proofL : ConvertProof ⊕ CombineProof
  proofR : ConvertProof ⊕ CombineProof
  Smid : CommittedVMState VC
  NL : ℕ
  NR : ℕ

/-- Boundary statement: initial and final *full-memory* states.

Paper: full-state boundaries in `def:cte` (ch05). -/
structure FinalStmtFull (VC : VectorCommitment) where
  S0 : FullVMState VC
  ST : FullVMState VC

/-- Commit a full state's memory, yielding the corresponding committed state. -/
def toCommitted {VC : VectorCommitment} (S : FullVMState VC) : CommittedVMState VC :=
  ⟨S.pc, S.regs, VC.commit S.mem⟩

/-! ## System -/

/-- The multi-step recursion system. The leaf SNARK is abstract: KS of the leaf
gives a `SegWitness` (the intermediate committed states), keeping the recursion
tower independent of the bus.

Paper: ch04 recursion tower, parameterized over an abstract leaf. -/
structure System where
  VC : VectorCommitment
  Nseg : ℕ
  T : ℕ
  memFreePred : MemFreePredicate
  hNseg : 0 < Nseg
  hDvd : Nseg ∣ T
  hT : T ≥ 2 * Nseg
  LeafProof : Type
  leafVerify : RecStmt VC → LeafProof → Prop
  ConvertProof : Type
  convertVerify : RecStmt VC → ConvertProof → Prop
  CombineProof : Type
  combineVerify : RecStmt VC → CombineProof → Prop
  EmbedProof : Type
  embedVerify : EmbedStmt VC → EmbedProof → Prop

namespace System

variable (sys : System)

def m : ℕ := sys.T / sys.Nseg

theorem m_ge_two : sys.m ≥ 2 :=
  (Nat.le_div_iff_mul_le sys.hNseg).mpr sys.hT

theorem m_pos : 0 < sys.m := Nat.lt_of_lt_of_le (by omega) sys.m_ge_two

theorem T_eq : sys.T = sys.m * sys.Nseg :=
  (Nat.div_mul_cancel sys.hDvd).symm

/-! ## Relations -/

/-- The leaf relation: a trace of `Nseg` committed steps from `S0` to `SN`,
each certified by its `MemStep` witness. Knowledge soundness of the leaf SNARK
extracts the intermediate committed states.

Paper: the segment-level relation; `R_{0,step}` simplified (no bus). -/
def RLeaf : Relation where
  Stmt := RecStmt sys.VC
  Wit := SegWitness sys.VC
  rel := fun st w =>
    w.states 0 = st.S0 ∧
    w.states sys.Nseg = st.SN ∧
    ∀ j, j < sys.Nseg →
      CommittedMemory.step sys.memFreePred (w.states j) (w.states (j + 1)) (w.steps j)

/-- The leaf argument system. -/
def ASLeaf : ArgumentSystem sys.RLeaf where
  Proof := sys.LeafProof
  verify := sys.leafVerify

/-- `R_2` **convert** (1-to-1): wraps a leaf proof, enforcing `N = Nseg`.

Paper: `lem:convert` (ch04). -/
def RConvert : Relation where
  Stmt := RecStmt sys.VC
  Wit := sys.LeafProof
  rel := fun st p => sys.leafVerify st p ∧ st.N = sys.Nseg

/-- Argument system `Π_2` for convert. -/
def ASConvert : ArgumentSystem sys.RConvert where
  Proof := sys.ConvertProof
  verify := sys.convertVerify

/-- `R_3` **combine** (binary 2-to-1): two children, each accepted by either
`Π_convert` or `Π_combine`, chained through a midpoint. Side conditions enforce
well-foundedness (`rem:wellfounded`): `N_L + N_R = N` with both `≥ Nseg` and
divisible by `Nseg`, so each child's step count is strictly less than the
parent's.

Paper: `lem:combine` (ch04). -/
def RCombine : Relation where
  Stmt := RecStmt sys.VC
  Wit := CombineWitness sys.VC sys.ConvertProof sys.CombineProof
  rel := fun st w =>
    (match w.proofL with
     | .inl p => sys.convertVerify ⟨st.S0, w.Smid, w.NL⟩ p
     | .inr p => sys.combineVerify ⟨st.S0, w.Smid, w.NL⟩ p) ∧
    (match w.proofR with
     | .inl p => sys.convertVerify ⟨w.Smid, st.SN, w.NR⟩ p
     | .inr p => sys.combineVerify ⟨w.Smid, st.SN, w.NR⟩ p) ∧
    w.NL + w.NR = st.N ∧
    sys.Nseg ∣ w.NL ∧ sys.Nseg ∣ w.NR ∧
    w.NL ≥ sys.Nseg ∧ w.NR ≥ sys.Nseg

/-- Argument system `Π_3` for combine. -/
def ASCombine : ArgumentSystem sys.RCombine where
  Proof := sys.CombineProof
  verify := sys.combineVerify

/-- `R_4` **embed** (final): wraps a combine proof for the full execution.

Paper: `lem:embed` (ch04). -/
def REmbed : Relation where
  Stmt := EmbedStmt sys.VC
  Wit := sys.CombineProof
  rel := fun st p => sys.combineVerify ⟨st.S0, st.ST, sys.T⟩ p

/-- Argument system `Π_4` for embed. -/
def ASEmbed : ArgumentSystem sys.REmbed where
  Proof := sys.EmbedProof
  verify := sys.embedVerify

/-! ## Trust base -/

/-- The trust base: knowledge soundness of all four SNARKs.

Paper: the assumptions charged in `thm:main` (ch05). -/
structure Assumptions (sys : System) : Prop where
  ksLeaf : KnowledgeSound sys.ASLeaf
  ksCombine : KnowledgeSound sys.ASCombine
  ksConvert : KnowledgeSound sys.ASConvert
  ksEmbed : KnowledgeSound sys.ASEmbed

/-! ## Committed trace validity -/

/-- A trace of `N` committed steps from `S0` to `SN`, each certified by
`committedStep`. -/
def CommittedTraceValid (S0 SN : CommittedVMState sys.VC)
    (Ŝ : ℕ → CommittedVMState sys.VC) (N : ℕ) : Prop :=
  Ŝ 0 = S0 ∧ Ŝ N = SN ∧
  ∀ k, k < N → committedStep sys.memFreePred (Ŝ k) (Ŝ (k + 1))

/-! ## Tree-unrolling extraction

Builds a committed trace by recursing on the step count `N`. At a leaf
(`N = Nseg`), extracts through convert → leaf to get the segment's committed
trace. At an internal node (`N > Nseg`), extracts through combine to get child
proofs and midpoint, then recurses on both halves and stitches. The guard
`NL < N` / `NR < N` ensures totality; for verifying proofs the combine
relation's side conditions guarantee this.

Paper: `lem:combine` tree unrolling (ch04), `rem:wellfounded`. -/

/-- **Tree-unrolling extraction.** If the leaf, convert, and
combine SNARKs are knowledge-sound, any accepting convert-or-combine proof
for `N` steps yields a valid committed trace. Proved by well-founded
induction on `N`.

Paper: `lem:combine` (ch04). The `(m-1)` combine coefficient arises because
`RecTree.internals_eq_leaves_sub_one` counts exactly `m - 1` internal
(combine) nodes for `m` leaves (segments). -/
theorem combine_tree
    (ksLeaf : KnowledgeSound sys.ASLeaf)
    (ksConvert : KnowledgeSound sys.ASConvert)
    (ksCombine : KnowledgeSound sys.ASCombine)
    (S0 SN : CommittedVMState sys.VC) (N : ℕ)
    (hN_dvd : sys.Nseg ∣ N) (hN_ge : N ≥ sys.Nseg)
    (p : sys.ConvertProof ⊕ sys.CombineProof)
    (hverify : match p with
     | .inl cp => sys.convertVerify ⟨S0, SN, N⟩ cp
     | .inr cp => sys.combineVerify ⟨S0, SN, N⟩ cp) :
    ∃ Ŝ : ℕ → CommittedVMState sys.VC,
      sys.CommittedTraceValid S0 SN Ŝ N := by
  obtain ⟨El, hEl⟩ := ksLeaf
  obtain ⟨Ecb, hEcb⟩ := ksCombine
  obtain ⟨Ec, hEc⟩ := ksConvert
  -- Strong induction on N, quantifying over all inputs
  suffices ∀ (N : ℕ), ∀ (S0 SN : CommittedVMState sys.VC),
      sys.Nseg ∣ N → N ≥ sys.Nseg →
      ∀ (p : sys.ConvertProof ⊕ sys.CombineProof),
      (match p with
       | .inl cp => sys.convertVerify ⟨S0, SN, N⟩ cp
       | .inr cp => sys.combineVerify ⟨S0, SN, N⟩ cp) →
      ∃ Ŝ, sys.CommittedTraceValid S0 SN Ŝ N from this N S0 SN hN_dvd hN_ge p hverify
  intro N
  induction N using Nat.strongRecOn with
  | _ N ih =>
  intro S0 SN hN_dvd hN_ge p hverify
  by_cases hle : N ≤ sys.Nseg
  · -- **Leaf.** N = Nseg (since N ≥ Nseg ∧ N ≤ Nseg).
    have hNeq : N = sys.Nseg := le_antisymm hle hN_ge
    have hcv : ∃ cp, sys.convertVerify ⟨S0, SN, N⟩ cp := by
      cases p with
      | inl cp => exact ⟨cp, hverify⟩
      | inr cp =>
        have hrel := hEcb ⟨S0, SN, N⟩ cp hverify
        dsimp only [RCombine] at hrel
        obtain ⟨_, _, hsum, _, _, hNL, hNR⟩ := hrel
        exfalso; have := sys.hNseg; omega
    obtain ⟨cp, hcpv⟩ := hcv
    have hrel_c := hEc ⟨S0, SN, N⟩ cp hcpv
    dsimp only [RConvert] at hrel_c
    obtain ⟨hleaf_v, _⟩ := hrel_c
    have hrel_l := hEl ⟨S0, SN, N⟩ _ hleaf_v
    dsimp only [RLeaf] at hrel_l
    obtain ⟨hstart, hend, hstep_rel⟩ := hrel_l
    set w := El.extract ⟨S0, SN, N⟩ (Ec.extract ⟨S0, SN, N⟩ cp)
    refine ⟨w.states, hstart, ?_, ?_⟩
    · rw [hNeq]; exact hend
    · intro k hk
      rw [hNeq] at hk
      exact ⟨w.steps k, hstep_rel k hk⟩
  · -- **Node.** N > Nseg — extract through combine, then recurse.
    have hNgt : N > sys.Nseg := Nat.lt_of_not_le hle
    have hcbv : ∃ cp, sys.combineVerify ⟨S0, SN, N⟩ cp := by
      cases p with
      | inr cp => exact ⟨cp, hverify⟩
      | inl cp =>
        have hrel := hEc ⟨S0, SN, N⟩ cp hverify
        dsimp only [RConvert] at hrel
        omega
    obtain ⟨cp, hcpv⟩ := hcbv
    have hrel := hEcb ⟨S0, SN, N⟩ cp hcpv
    dsimp only [RCombine] at hrel
    set w := Ecb.extract ⟨S0, SN, N⟩ cp
    obtain ⟨hvL, hvR, hsum, hdvL, hdvR, hgeL, hgeR⟩ := hrel
    have hNseg_pos := sys.hNseg
    have hNL_lt : w.NL < N := by omega
    have hNR_lt : w.NR < N := by omega
    -- Recurse on both subtrees
    have ⟨ŜL, hŜL⟩ := ih w.NL hNL_lt S0 w.Smid hdvL hgeL w.proofL hvL
    have ⟨ŜR, hŜR⟩ := ih w.NR hNR_lt w.Smid SN hdvR hgeR w.proofR hvR
    obtain ⟨hL0, hLN, hLstep⟩ := hŜL
    obtain ⟨hR0, hRN, hRstep⟩ := hŜR
    -- Stitch the two traces: left [0, NL], right [0, NR] → combined [0, N]
    refine ⟨fun k => if k ≤ w.NL then ŜL k else ŜR (k - w.NL), ?_, ?_, ?_⟩
    · -- Start: k = 0 ≤ NL
      simp only [Nat.zero_le, ↓reduceIte]; exact hL0
    · -- End: k = N > NL
      have hN_gt_NL : ¬ (N ≤ w.NL) := by omega
      simp only [hN_gt_NL, ↓reduceIte]
      have hN_sub : N - w.NL = w.NR := by omega
      rw [hN_sub]; exact hRN
    · -- Steps: case split on whether we're in the left, seam, or right portion
      intro k hk
      dsimp only
      by_cases hk1 : k + 1 ≤ w.NL
      · -- Both k and k+1 in the left trace
        have hk0 : k ≤ w.NL := by omega
        simp only [hk0, hk1, ↓reduceIte]
        exact hLstep k (by omega)
      · -- k+1 > NL
        by_cases hk2 : k ≤ w.NL
        · -- Seam: k ≤ NL but k+1 > NL, so k = NL
          have hkeq : k = w.NL := le_antisymm hk2 (by omega)
          subst hkeq
          simp only [le_refl, hk1, ↓reduceIte]
          have hsub : w.NL + 1 - w.NL = 1 := by omega
          rw [hsub, hLN, ← hR0]
          exact hRstep 0 (by omega)
        · -- Both in the right trace
          simp only [hk2, hk1, ↓reduceIte]
          have hsub : k + 1 - w.NL = (k - w.NL) + 1 := by omega
          rw [hsub]
          exact hRstep (k - w.NL) (by omega)

/-! ## The committed-trace extraction -/

/-- **Committed-trace extraction.** If all four SNARKs are knowledge-sound,
every accepting embed proof yields a committed trace from `x.S0` to `x.ST` of
length `T`.

Paper: `lem:embed` composed with `lem:combine` tree unrolling (ch04). -/
theorem committedTrace_extract (h : sys.Assumptions) :
    ∀ (x : EmbedStmt sys.VC) (p : sys.EmbedProof),
      sys.embedVerify x p →
      ∃ Ŝ : ℕ → CommittedVMState sys.VC,
        sys.CommittedTraceValid x.S0 x.ST Ŝ sys.T := by
  obtain ⟨ksLeaf, ksCombine, ksConvert, ksEmbed⟩ := h
  obtain ⟨Ee, hEe⟩ := ksEmbed
  intro x p hp
  have hrel := hEe x p hp
  dsimp only [REmbed] at hrel
  have hge : sys.T ≥ sys.Nseg := le_trans (Nat.le_mul_of_pos_left sys.Nseg (by omega)) sys.hT
  exact sys.combine_tree ksLeaf ksConvert ksCombine x.S0 x.ST sys.T sys.hDvd hge
    (.inr (Ee.extract x p)) hrel

/-! ## The zkVM -/

/-- **The multi-step zkVM.** Its state is the *full-memory* VM state; its
step is `∃ w, FullMemory.step …`; its statement carries full boundary states;
its verifier commits the boundaries and defers to the embed SNARK.

Paper: `def:cte` and `prop:memory-extractability` (ch05). This replaces the
two-step toy with the paper's recursion tower but still omits the bus and
concrete ISA. -/
def toZkVM : ZkVM where
  State := FullVMState sys.VC
  step := fun S₁ S₂ => ∃ w, FullMemory.step sys.memFreePred S₁ S₂ w
  T := sys.T
  Stmt := FinalStmtFull sys.VC
  initial := FinalStmtFull.S0
  terminal := FinalStmtFull.ST
  Proof := sys.EmbedProof
  verify := fun x p => sys.embedVerify ⟨toCommitted x.S0, toCommitted x.ST⟩ p

/-- Step interface for this VM: `CommitInv` is the representation relation,
`committedStep` the binary committed predicate. -/
def memoryStepInterface : StepInterface sys.toZkVM where
  CommittedState := CommittedVMState sys.VC
  represents := CommitInv
  stepCommitted := committedStep sys.memFreePred

/-- `StepInterface.MemoryBridge` for this VM.

Paper: `prop:memory-extractability`, `rem:mem-inheritance`, `thm:main` Step 6
(ch05). -/
theorem memoryBridge
    (hComplete : sys.VC.Complete) (hpos : sys.VC.PositionBinding)
    (hupd : sys.VC.UpdateBinding) :
    sys.memoryStepInterface.MemoryBridge := by
  intro Ŝ₁ Ŝ₂ S₁ hInv hstep
  simpa [memoryStepInterface, toZkVM] using
    (step_reconstruct hComplete hpos hupd sys.memFreePred S₁ Ŝ₁ Ŝ₂ hInv hstep)

/-! ## The Memory ↔ MultiStep bridge -/

/-- A valid committed trace yields a valid full-memory trace. Restates
`Memory.trace_mem_extract` in terms of `CommittedTraceValid` and `TraceValid`.

Paper: `prop:memory-extractability` and `rem:mem-inheritance` (ch05). -/
theorem traceValid_full
    (hComplete : sys.VC.Complete) (hpos : sys.VC.PositionBinding)
    (hupd : sys.VC.UpdateBinding)
    (x : FinalStmtFull sys.VC) (Ŝ : ℕ → CommittedVMState sys.VC)
    (hval : sys.CommittedTraceValid (toCommitted x.S0) (toCommitted x.ST) Ŝ sys.T) :
    sys.toZkVM.TraceValid x
      (reconstructTrace Ŝ (chooseMemStep sys.memFreePred Ŝ) x.S0) := by
  obtain ⟨hstart, hend, hsteprel⟩ := hval
  have hseed : CommitInv (Ŝ 0) x.S0 := by rw [hstart]; exact ⟨rfl, rfl, rfl⟩
  have hstepC : ∀ k, k < sys.T →
      CommittedMemory.step sys.memFreePred (Ŝ k) (Ŝ (k + 1))
        (chooseMemStep sys.memFreePred Ŝ k) :=
    fun k hk => chooseMemStep_spec sys.memFreePred Ŝ k (hsteprel k hk)
  obtain ⟨hinv, hstepF⟩ :=
    trace_mem_extract hComplete hpos hupd sys.memFreePred sys.T Ŝ
      (chooseMemStep sys.memFreePred Ŝ) x.S0 hseed hstepC
  refine ⟨rfl, ?_, ?_⟩
  · show reconstructTrace Ŝ (chooseMemStep sys.memFreePred Ŝ) x.S0 sys.T = x.ST
    set ST' := reconstructTrace Ŝ (chooseMemStep sys.memFreePred Ŝ) x.S0 sys.T with hST'
    have hci : CommitInv (Ŝ sys.T) ST' := hinv sys.T (le_refl _)
    rw [hend] at hci
    simp only [toCommitted] at hci
    obtain ⟨hpc, hreg, hmem⟩ := hci
    have e3 : ST'.mem = x.ST.mem := mem_eq_of_commit_eq hComplete hpos hmem
    calc ST' = (⟨ST'.pc, ST'.regs, ST'.mem⟩ : FullVMState sys.VC) := rfl
      _ = ⟨x.ST.pc, x.ST.regs, x.ST.mem⟩ := by rw [← hpc, ← hreg, e3]
      _ = x.ST := rfl
  · intro i hi
    exact ⟨_, hstepF i hi⟩

/-- **CTE for the multi-step VM.** Under KS of all four SNARKs and the memory
commitment binding assumptions, the multi-step VM is correct-trace extractable
over full-memory states.

Paper: `def:cte`, `prop:memory-extractability`, `rem:mem-inheritance` (ch05),
and `lem:convert`/`combine`/`embed` (ch04). -/
theorem cte (h : sys.Assumptions)
    (hComplete : sys.VC.Complete) (hpos : sys.VC.PositionBinding)
    (hupd : sys.VC.UpdateBinding) :
    sys.toZkVM.CTE := by
  classical
  -- CTE = ∃ E, ∀ x p, verify x p → TraceValid x (E x p)
  -- The toZkVM.verify wraps embedVerify with committed boundaries.
  -- First show the weak form, then Skolemize.
  have weak : ∀ (x : sys.toZkVM.Stmt) (p : sys.toZkVM.Proof),
      sys.toZkVM.verify x p → ∃ tr, sys.toZkVM.TraceValid x tr := by
    intro x p hp
    change sys.embedVerify ⟨toCommitted x.S0, toCommitted x.ST⟩ p at hp
    obtain ⟨Ŝ, hŜ⟩ := sys.committedTrace_extract h
      ⟨toCommitted x.S0, toCommitted x.ST⟩ p hp
    exact ⟨_, sys.traceValid_full hComplete hpos hupd x Ŝ hŜ⟩
  -- Skolemize: from ∀ x p, verify → ∃ tr, ... to ∃ E, ∀ x p, verify → ...
  -- Use Classical.choice to pick the trace for each (x, p).
  refine ⟨fun x p => if h : sys.toZkVM.verify x p
    then (weak x p h).choose
    else fun _ => sys.toZkVM.initial x, ?_⟩
  intro x p hp
  simp only [hp, ↓reduceDIte]
  exact (weak x p hp).choose_spec

end System
end MultiStep
end VanillaZkVM
