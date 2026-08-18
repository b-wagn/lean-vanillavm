import VanillaZkVM.Preliminaries.Trace
import VanillaZkVM.Specification.Cte
import VanillaZkVM.VMs.Memory
import VanillaZkVM.VMs.Step

/-!
# A minimal "two-step" zkVM, instantiating the abstract system

A stripped-down system that keeps the two features that make the security
argument non-trivial — composing straight-line extraction across SNARK layers,
and committed-memory states — while dropping the bus, the four inner circuits,
the chips, and the binary `convert`/`combine`/`embed` tower.

* Segment layer `RSeg`: a trace of `Nseg` committed steps `Sin → Sout` under the
  committed step predicate `CommittedMemory.step` (from `Memory`). Each step carries
  its explicit `MemStep` witness, including the opening used by a read/write.
  Operations are not deferred to a bus.
* Final layer `RFinal`: a single SNARK merging `m` segment proofs whose boundary
  states chain `S0 → ST`.

The VM is `toZkVM`: its states are *full-memory* VM states, `T = m * Nseg`, and its
verifier commits the claimed boundary states before deferring to the final SNARK.
`cte` proves `CTE` for it.

The proof has two halves, with the committed-memory layer as the object passed
between them:

1. `committedTrace_extract` — the SNARK half. Two-layer straight-line extraction
   (`RFinal` witness, then an `RSeg` witness per segment) produces a trace of
   *committed* states satisfying `CommittedTraceValid`. The trace is built with
   `concatTrace` and its validity rests on `chain_flatten` (both from `Trace`). Its
   binary step is the existential projection `committedStep` of the witness-indexed
   `CommittedMemory.step`, with the per-step `MemStep` witnesses retained in the
   segment witnesses.
2. `traceValid_full` — the memory half. `Memory.trace_mem_extract` reconstructs a
   full-memory trace along that committed trace, satisfying `CommitInv` at every
   state and `FullMemory.step` at every step.

Traces are `ℕ`-indexed with `< bound` conditions (uniform with `Rstar`,
and it makes concatenation pure `ℕ`-arithmetic).
-/

namespace VanillaZkVM
namespace TwoStep

/-! ## Statements and witnesses -/

/-- Segment statement: the committed boundary states. -/
structure SegStmt (VC : VectorCommitment) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC

/-- Segment witness: the intermediate committed states and one explicit
`MemStep` witness per transition, both `ℕ`-indexed (only the first `Nseg + 1`
states and `Nseg` steps matter). `MemStep.read` and `MemStep.write` values carry
the openings that memory extraction must expose. -/
structure SegWitness (VC : VectorCommitment) where
  states : ℕ → CommittedVMState VC
  steps : ℕ → MemStep VC

/-- Final statement: the committed boundary states of the whole execution. -/
structure FinalStmt (VC : VectorCommitment) where
  S0 : CommittedVMState VC
  ST : CommittedVMState VC

/-- Final witness: `m` segment proofs and the boundary states they connect. -/
structure FinalWitness (VC : VectorCommitment) (SegProof : Type) where
  boundary : ℕ → CommittedVMState VC
  proofs : ℕ → SegProof

/-- Boundary statement of the VM: the initial and final *full* states. `toZkVM`
uses it as its `Stmt`, and its verifier commits both states so that the final
SNARK — which speaks about committed states — can check them.

Paper: full-state boundaries in `def:cte` (ch05). -/
structure FinalStmtFull (VC : VectorCommitment) where
  S0 : FullVMState VC
  ST : FullVMState VC

/-- Commit a full state's memory, yielding the corresponding committed state. -/
def toCommitted {VC : VectorCommitment} (S : FullVMState VC) : CommittedVMState VC :=
  ⟨S.pc, S.regs, VC.commit S.mem⟩

/-! ## The toy system -/

/-- The toy system: a memory commitment scheme, the memory-free component of
its step semantics, and the two layers' proof types with their
verifiers. -/
structure System where
  VC : VectorCommitment
  Nseg : ℕ
  m : ℕ
  /-- Memory-free register/program-counter part of each step; the full
  committed step is `CommittedMemory.step memFreePred` (from `Memory`). -/
  memFreePred : MemFreePredicate
  SegProof : Type
  segVerify : SegStmt VC → SegProof → Prop
  FinalProof : Type
  finalVerify : FinalStmt VC → FinalProof → Prop

namespace System

variable (sys : System)

/-- Segment relation `RSeg`: a trace of `Nseg` committed steps from `Sin` to
`Sout`, each certified by its explicit `MemStep` witness. -/
def RSeg : Relation where
  Stmt := SegStmt sys.VC
  Wit := SegWitness sys.VC
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states sys.Nseg = st.Sout ∧
    ∀ j, j < sys.Nseg →
      CommittedMemory.step sys.memFreePred (w.states j) (w.states (j + 1)) (w.steps j)

/-- The segment argument system `Π_seg`. -/
def ASSeg : ArgumentSystem sys.RSeg where
  Proof := sys.SegProof
  verify := sys.segVerify

/-- Final relation `RFinal`: `m` segment proofs, each accepted by `Π_seg`, whose
boundary states chain from `S0` to `ST`. -/
def RFinal : Relation where
  Stmt := FinalStmt sys.VC
  Wit := FinalWitness sys.VC sys.SegProof
  rel := fun st w =>
    w.boundary 0 = st.S0 ∧
    w.boundary sys.m = st.ST ∧
    ∀ i, i < sys.m →
      sys.segVerify ⟨w.boundary i, w.boundary (i + 1)⟩ (w.proofs i)

/-- The final argument system `Π_final`. -/
def ASFinal : ArgumentSystem sys.RFinal where
  Proof := sys.FinalProof
  verify := sys.finalVerify

/-! ## The committed-memory trace

Two-layer extraction first recovers a trace of *committed* states. It is an
intermediate: memory reconstruction consumes it and produces the full-memory trace
that the VM's `CTE` talks about. A plain predicate is therefore all it needs — the
security claims are made about `toZkVM`, not about this. -/

/-- A trace of `m * Nseg` committed steps running from `x.S0` to `x.ST`, every
step certified by `committedStep`.

This is the committed-level analogue of `ZkVM.TraceValid`. It is spelled out here
because the committed layer carries no `ZkVM` of its own. -/
def CommittedTraceValid (x : FinalStmt sys.VC) (Ŝ : ℕ → CommittedVMState sys.VC) : Prop :=
  Ŝ 0 = x.S0 ∧ Ŝ (sys.m * sys.Nseg) = x.ST ∧
  ∀ k, k < sys.m * sys.Nseg → committedStep sys.memFreePred (Ŝ k) (Ŝ (k + 1))

/-! ## The zkVM -/

/-- **The two-step zkVM.** Its state is the *full-memory* VM state, a step is
`∃ w, FullMemory.step …` (the full-memory step relation), the statement carries
full boundary states, and the verifier commits those boundaries and defers to the
final SNARK. `CTE` of this instance is the full-memory correct-trace
extractability statement — a concrete instance of the abstract `CTE`.

Paper: `def:cte` and `prop:memory-extractability` (ch05). This toy omits the bus,
concrete ISA, and recursive convert/combine/embed layers. -/
def toZkVM : ZkVM where
  State := FullVMState sys.VC
  step := fun S₁ S₂ => ∃ w, FullMemory.step sys.memFreePred S₁ S₂ w
  T := sys.m * sys.Nseg
  Stmt := FinalStmtFull sys.VC
  initial := FinalStmtFull.S0
  terminal := FinalStmtFull.ST
  Proof := sys.FinalProof
  verify := fun x p => sys.finalVerify ⟨toCommitted x.S0, toCommitted x.ST⟩ p

/-- This VM's instance of the frozen step contract (`StepInterface`). `CommitInv` is
the representation relation and `committedStep` the binary committed predicate;
`MemStep` witnesses stay hidden behind the latter's existential.

This is Lean-side coordination for `prop:memory-extractability`, not an additional
paper security definition. -/
def memoryStepInterface : StepInterface sys.toZkVM where
  CommittedState := CommittedVMState sys.VC
  represents := CommitInv
  stepCommitted := committedStep sys.memFreePred

/-- `StepInterface.MemoryBridge` for this VM. Completeness, position binding, and
update binding let `step_reconstruct` construct a represented next full-memory
state satisfying the canonical `sys.toZkVM.step` predicate.

Paper: `prop:memory-extractability`, `rem:mem-inheritance`, and Step 6 of
`thm:main` (ch05), specialized to the two-step toy. -/
theorem memoryBridge
    (hComplete : sys.VC.Complete) (hpos : sys.VC.PositionBinding)
    (hupd : sys.VC.UpdateBinding) :
    sys.memoryStepInterface.MemoryBridge := by
  intro Ŝ₁ Ŝ₂ S₁ hInv hstep
  simpa [memoryStepInterface, toZkVM] using
    (step_reconstruct hComplete hpos hupd sys.memFreePred S₁ Ŝ₁ Ŝ₂ hInv hstep)

/-- **Trust base for the two-step zkVM** — the single surface collecting the
unproven assumptions `committedTrace_extract` relies on. This toy system uses no bus, so its trust
base is exactly the two SNARKs' knowledge soundness. The full-memory statement
`cte` additionally consumes the memory-commitment binding assumptions
(`Complete`/`PositionBinding`/`UpdateBinding`), which are passed separately rather
than bundled here. The well-formedness side condition `0 < Nseg` is *not* part of
the trust base and stays a separate argument. -/
structure Assumptions (sys : System) : Prop where
  /-- Knowledge soundness of the segment SNARK `Π_seg`. -/
  ksSeg : KnowledgeSound sys.ASSeg
  /-- Knowledge soundness of the final merging SNARK `Π_final`. -/
  ksFinal : KnowledgeSound sys.ASFinal

/-- **The `Memory` ↔ `TwoStep` bridge** — a valid committed trace yields a valid
*full-memory* trace of `toZkVM`: the reconstructed trace
`reconstructTrace Ŝ (chooseMemStep …) x.S0` is `toZkVM`-valid whenever `Ŝ`
satisfies `CommittedTraceValid` for the committed boundaries of `x`.

The two modules split the work: `Memory` reconstructs full memory over raw
states (`CommitInv`, `MemStep`, the committed/full step predicates) and knows
nothing of SNARKs or the abstract `ZkVM`; this file defines the `ZkVM` instance
but proves nothing about memory. This theorem joins them, restating
`Memory.trace_mem_extract` in terms of `CommittedTraceValid` and `TraceValid`
alone, so `cte` below never touches the memory internals.

The terminal state matches `x.ST` because `CommitInv` at the last state plus
injectivity of `commit` (`mem_eq_of_commit_eq`) determines its memory.

Paper: `prop:memory-extractability` and `rem:mem-inheritance` (ch05), composed
with the two-layer toy trace. -/
theorem traceValid_full
    (hComplete : sys.VC.Complete) (hpos : sys.VC.PositionBinding)
    (hupd : sys.VC.UpdateBinding)
    (x : FinalStmtFull sys.VC) (Ŝ : ℕ → CommittedVMState sys.VC)
    (hval : sys.CommittedTraceValid ⟨toCommitted x.S0, toCommitted x.ST⟩ Ŝ) :
    sys.toZkVM.TraceValid x
      (reconstructTrace Ŝ (chooseMemStep sys.memFreePred Ŝ) x.S0) := by
  obtain ⟨hstart, hend, hsteprel⟩ := hval
  have hstartc : Ŝ 0 = toCommitted x.S0 := hstart
  have hendc : Ŝ (sys.m * sys.Nseg) = toCommitted x.ST := hend
  -- the invariant seed holds definitionally (committed initial = commit of full initial)
  have hseed : CommitInv (Ŝ 0) x.S0 := by rw [hstartc]; exact ⟨rfl, rfl, rfl⟩
  -- Pick `MemStep` witnesses and apply `Memory.trace_mem_extract`.
  have hstepC : ∀ k, k < sys.m * sys.Nseg →
      CommittedMemory.step sys.memFreePred (Ŝ k) (Ŝ (k + 1))
        (chooseMemStep sys.memFreePred Ŝ k) :=
    fun k hk => chooseMemStep_spec sys.memFreePred Ŝ k (hsteprel k hk)
  obtain ⟨hinv, hstepF⟩ :=
    trace_mem_extract hComplete hpos hupd sys.memFreePred (sys.m * sys.Nseg) Ŝ
      (chooseMemStep sys.memFreePred Ŝ) x.S0 hseed hstepC
  refine ⟨rfl, ?_, ?_⟩
  · -- terminal state equals `x.ST`
    show reconstructTrace Ŝ (chooseMemStep sys.memFreePred Ŝ) x.S0 (sys.m * sys.Nseg) = x.ST
    set ST' := reconstructTrace Ŝ (chooseMemStep sys.memFreePred Ŝ) x.S0
      (sys.m * sys.Nseg) with hST'
    have hci : CommitInv (Ŝ (sys.m * sys.Nseg)) ST' := hinv (sys.m * sys.Nseg) (le_refl _)
    rw [hendc] at hci
    simp only [toCommitted] at hci
    obtain ⟨hpc, hreg, hmem⟩ := hci
    have e3 : ST'.mem = x.ST.mem := mem_eq_of_commit_eq hComplete hpos hmem
    calc ST' = (⟨ST'.pc, ST'.regs, ST'.mem⟩ : FullVMState sys.VC) := rfl
      _ = ⟨x.ST.pc, x.ST.regs, x.ST.mem⟩ := by rw [← hpc, ← hreg, e3]
      _ = x.ST := rfl
  · -- every step is a full-memory step
    intro i hi
    exact ⟨_, hstepF i hi⟩

/-- **Two-layer committed-trace extraction.** If both SNARKs are knowledge-sound
(and segments are non-empty), every accepting final proof yields a committed trace
from `x.S0` to `x.ST`. The extractor runs the two-layer straight-line extraction —
`RFinal` witness, then an `RSeg` witness per segment — and concatenates the
resulting committed sub-traces. Validity of the concatenation is `chain_flatten`.

This is the SNARK-composition half of `cte`. Its conclusion is a committed trace,
which `traceValid_full` then lifts to the full-memory trace `cte` needs. -/
theorem committedTrace_extract (hNseg : 0 < sys.Nseg) (h : sys.Assumptions) :
    ∃ E : FinalStmt sys.VC → sys.FinalProof → (ℕ → CommittedVMState sys.VC),
      ∀ (x : FinalStmt sys.VC) (p : sys.FinalProof),
        sys.finalVerify x p → sys.CommittedTraceValid x (E x p) := by
  obtain ⟨hseg, hfinal⟩ := h
  obtain ⟨Ef, hEf⟩ := hfinal
  obtain ⟨Es, hEs⟩ := hseg
  -- The trace-extractor: extract the RFinal witness, then flatten the per-segment
  -- RSeg witnesses.
  refine ⟨fun x p =>
      concatTrace sys.Nseg (Ef.extract x p).boundary
        (fun i j => (Es.extract ⟨(Ef.extract x p).boundary i,
                                 (Ef.extract x p).boundary (i + 1)⟩
                      ((Ef.extract x p).proofs i)).states j) sys.m, ?_⟩
  intro x p hp
  -- Layer 1: unpack the RFinal extraction.
  obtain ⟨hb0, hbm, hbver⟩ := hEf x p hp
  set d := (Ef.extract x p).boundary with hd
  set seg := (fun i j =>
      (Es.extract ⟨d i, d (i + 1)⟩ ((Ef.extract x p).proofs i)).states j) with hs
  -- Layer 2: each segment i < m yields a valid RSeg trace.
  have h0 : ∀ i, i < sys.m → seg i 0 = d i :=
    fun i hi => (hEs _ _ (hbver i hi)).1
  have hlast : ∀ i, i < sys.m → seg i sys.Nseg = d (i + 1) :=
    fun i hi => (hEs _ _ (hbver i hi)).2.1
  -- Each committed step is certified by its extracted `MemStep` witness; the
  -- abstract trace only needs the existential projection `committedStep`.
  have hstep : ∀ i, i < sys.m → ∀ j, j < sys.Nseg →
      committedStep sys.memFreePred (seg i j) (seg i (j + 1)) :=
    fun i hi j hj =>
      ⟨(Es.extract ⟨d i, d (i + 1)⟩ ((Ef.extract x p).proofs i)).steps j,
       (hEs _ _ (hbver i hi)).2.2 j hj⟩
  -- Concatenate.
  obtain ⟨e0, eT, estep⟩ :=
    chain_flatten (committedStep sys.memFreePred) sys.Nseg sys.m hNseg d seg h0 hlast hstep
  refine ⟨?_, ?_, ?_⟩
  · show concatTrace sys.Nseg d seg sys.m 0 = x.S0
    rw [e0]; exact hb0
  · show concatTrace sys.Nseg d seg sys.m (sys.m * sys.Nseg) = x.ST
    rw [eT]; exact hbm
  · intro k hk
    exact estep k hk

/-- **CTE for the two-step VM** — `committedTrace_extract` upgraded across the
`Memory ↔ TwoStep` bridge (`traceValid_full`), as a concrete instance of the abstract
`CTE`: `sys.toZkVM.CTE`. Under the extraction hypotheses plus the commitment
binding assumptions, the two-step VM is correct-trace extractable *over full-memory
states* — the extractor turns every accepting final proof into a valid full-memory
trace with the claimed boundaries and `∃ w, FullMemory.step …` at every step.

Proof: from `committedTrace_extract` get the committed-trace extractor `E`; the full
extractor commits `x`'s boundaries, runs `E`, and reconstructs the full trace.
Correctness is then exactly `traceValid_full` applied to `E`'s committed trace.

Paper: `def:cte`, `prop:memory-extractability`, and `rem:mem-inheritance`
(ch05). This is a two-layer memory theorem, not the full VanillaVM main
theorem. -/
theorem cte (hNseg : 0 < sys.Nseg) (h : sys.Assumptions)
    (hComplete : sys.VC.Complete) (hpos : sys.VC.PositionBinding)
    (hupd : sys.VC.UpdateBinding) :
    sys.toZkVM.CTE := by
  obtain ⟨E, hE⟩ := sys.committedTrace_extract hNseg h
  exact ⟨fun x p =>
      reconstructTrace (E ⟨toCommitted x.S0, toCommitted x.ST⟩ p)
        (chooseMemStep sys.memFreePred
          (E ⟨toCommitted x.S0, toCommitted x.ST⟩ p)) x.S0,
    fun x p hp =>
      sys.traceValid_full hComplete hpos hupd x _
        (hE ⟨toCommitted x.S0, toCommitted x.ST⟩ p hp)⟩

end System
end TwoStep
end VanillaZkVM
