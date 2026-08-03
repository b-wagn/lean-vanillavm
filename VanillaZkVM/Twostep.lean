import VanillaZkVM.Memory
import VanillaZkVM.Trace
import VanillaZkVM.Step

/-!
# A minimal "two-step" zkVM, instantiating the abstract system

A stripped-down system that keeps the two features that make the security
argument non-trivial — composing straight-line extraction across SNARK layers,
and committed-memory states — while dropping the bus, the four inner circuits,
the chips, and the binary `convert`/`combine`/`embed` tower.

* Segment layer `RSeg`: a chain of `Nseg` committed steps `Sin → Sout` under the
  multi-option committed step predicate `stepC` (from `Memory`). Each step carries
  its explicit `MemStep` witness, including the opening used by a read/write.
  Operations are not deferred to a bus.
* Final layer `RFinal`: a single SNARK merging `m` segment proofs whose boundary
  states chain `S0 → ST`.

We then instantiate the abstract `ZkVM` (`State` = committed states,
`T = m * Nseg`) and prove `CTE`, via the equivalence with `KnowledgeSound ASstar`
plus a two-layer extraction. The committed trace is produced with `concatTrace`;
its validity rests on `chain_flatten` (both from `Trace`).

The base `cte` target is a committed-memory trace whose binary step is the
existential projection `stepRel` of the multi-option `stepC`, with the per-step
`MemStep` witnesses retained in the segment witnesses. `cte_full` then folds
`Memory.trace_mem_extract` over that trace to obtain the *full-memory* statement:
a full-memory trace satisfying the commitment invariant at every state and a
genuine `stepF` at every step. Traces are `ℕ`-indexed with `< bound` conditions
(uniform with `Rstar`, and it makes concatenation pure `ℕ`-arithmetic).
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
states and `Nseg` steps matter). Read/write step witnesses carry the openings that
memory extraction must expose. -/
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

/-- Full-memory boundary statement: the initial and final *full* states. Used by
the full-memory instantiation `toZkVMFull`, whose verifier commits these to reuse
the committed final SNARK. -/
structure FinalStmtFull (VC : VectorCommitment) where
  S0 : FullVMState VC
  ST : FullVMState VC

/-- Commit a full state's memory, yielding the corresponding committed state. -/
def toCommitted {VC : VectorCommitment} (S : FullVMState VC) : CommittedVMState VC :=
  ⟨S.pc, S.regs, VC.commit S.mem⟩

/-! ## The toy system -/

/-- The toy system: an assumed committed step predicate, a memory commitment
scheme, and the two layers' proof types with their verifiers. -/
structure System where
  VC : VectorCommitment
  Nseg : ℕ
  m : ℕ
  /-- Memory-free register/program-counter part shared by every step option; the
  full committed step is `stepC memFreePred` (from `Memory`). -/
  memFreePred : MemFreePredicate
  SegProof : Type
  segVerify : SegStmt VC → SegProof → Prop
  FinalProof : Type
  finalVerify : FinalStmt VC → FinalProof → Prop

namespace System

variable (sys : System)

/-- The binary committed-step relation the abstract ZkVM sees: a step holds iff
some `MemStep` witness certifies it under `stepC sys.memFreePred`. The witnesses
themselves are retained in `SegWitness.steps`, where memory extractability
(`Memory.step_mem_extract`) consumes them; the flattened abstract trace only
needs this binary relation. -/
def stepRel (Ŝ₁ Ŝ₂ : CommittedVMState sys.VC) : Prop :=
  ∃ w : MemStep sys.VC, stepC sys.memFreePred Ŝ₁ Ŝ₂ w

/-- Segment relation `RSeg`: a chain of `Nseg` committed steps from `Sin` to
`Sout`, each certified by its explicit `MemStep` witness. -/
def RSeg : Relation where
  Stmt := SegStmt sys.VC
  Wit := SegWitness sys.VC
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states sys.Nseg = st.Sout ∧
    ∀ j, j < sys.Nseg →
      stepC sys.memFreePred (w.states j) (w.states (j + 1)) (w.steps j)

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

/-- Instantiate the abstract zkVM: committed states, the assumed step predicate,
`T = m * Nseg`, boundary statements, and the final verifier. -/
def toZkVM : ZkVM where
  State := CommittedVMState sys.VC
  step := sys.stepRel
  T := sys.m * sys.Nseg
  Stmt := FinalStmt sys.VC
  initial := FinalStmt.S0
  terminal := FinalStmt.ST
  Proof := sys.FinalProof
  verify := sys.finalVerify

/-- **Full-memory instantiation.** Same VM, but the state is the *full-memory*
state, a step is `∃ w, stepF …` (the full-memory step relation), the statement
carries full boundary states, and the verifier commits them and defers to the
committed final SNARK. `CTE` of this instance is the full-memory correct-trace
extractability statement — a concrete instance of the abstract `CTE`. -/
def toZkVMFull : ZkVM where
  State := FullVMState sys.VC
  step := fun S₁ S₂ => ∃ w, stepF sys.memFreePred S₁ S₂ w
  T := sys.m * sys.Nseg
  Stmt := FinalStmtFull sys.VC
  initial := FinalStmtFull.S0
  terminal := FinalStmtFull.ST
  Proof := sys.FinalProof
  verify := fun x p => sys.finalVerify ⟨toCommitted x.S0, toCommitted x.ST⟩ p

/-- **Trust base for the two-step zkVM** — the single surface collecting the
unproven assumptions `cte` relies on. This toy system uses no bus, so its trust
base is exactly the two SNARKs' knowledge soundness. The full-memory statement
`cte_full` additionally consumes the memory-commitment binding assumptions
(`Complete`/`PositionBinding`/`UpdateBinding`), which are passed separately rather
than bundled here. The well-formedness side condition `0 < Nseg` is *not* part of
the trust base and stays a separate argument. -/
structure Assumptions (sys : System) : Prop where
  /-- Knowledge soundness of the segment SNARK `Π_seg`. -/
  ksSeg : KnowledgeSound sys.ASSeg
  /-- Knowledge soundness of the final merging SNARK `Π_final`. -/
  ksFinal : KnowledgeSound sys.ASFinal

/-- **The fold, in ZkVM terms** — a valid *committed* trace of `toZkVM` yields a
valid *full-memory* trace of `toZkVMFull`. This is the `Memory ↔ Twostep` bridge
stated purely with `TraceValid`/`step`: the reconstructed trace
`reconstructTrace Ŝ (chooseStepWitness …) x.S0` is `toZkVMFull`-valid whenever `Ŝ` is
`toZkVM`-valid for the committed boundaries of `x`.

The commitment invariant along the trace is established internally by the generic
fold `Memory.trace_mem_extract`; the terminal state matches `x.ST` because the
invariant at the last state plus injectivity of `commit` (`mem_eq_of_commit_eq`)
pins its memory. -/
theorem traceValid_full
    (hComplete : Complete sys.VC) (hpos : PositionBinding sys.VC)
    (hupd : UpdateBinding sys.VC)
    (x : FinalStmtFull sys.VC) (Ŝ : ℕ → CommittedVMState sys.VC)
    (hval : sys.toZkVM.TraceValid ⟨toCommitted x.S0, toCommitted x.ST⟩ Ŝ) :
    sys.toZkVMFull.TraceValid x
      (reconstructTrace Ŝ (chooseStepWitness sys.memFreePred Ŝ) x.S0) := by
  obtain ⟨hstart, hend, hsteprel⟩ := hval
  have hstartc : Ŝ 0 = toCommitted x.S0 := hstart
  have hendc : Ŝ (sys.m * sys.Nseg) = toCommitted x.ST := hend
  -- the invariant seed holds definitionally (committed initial = commit of full initial)
  have hseed : CommitInv (Ŝ 0) x.S0 := by rw [hstartc]; exact ⟨rfl, rfl, rfl⟩
  -- pick step witnesses and run the generic fold
  have hstepC : ∀ k, k < sys.m * sys.Nseg →
      stepC sys.memFreePred (Ŝ k) (Ŝ (k + 1)) (chooseStepWitness sys.memFreePred Ŝ k) :=
    fun k hk => chooseStepWitness_spec sys.memFreePred Ŝ k (hsteprel k hk)
  obtain ⟨hinv, hstepF⟩ :=
    trace_mem_extract hComplete hpos hupd sys.memFreePred (sys.m * sys.Nseg) Ŝ
      (chooseStepWitness sys.memFreePred Ŝ) x.S0 hseed hstepC
  refine ⟨rfl, ?_, ?_⟩
  · -- terminal state equals `x.ST`
    show reconstructTrace Ŝ (chooseStepWitness sys.memFreePred Ŝ) x.S0 (sys.m * sys.Nseg) = x.ST
    set ST' := reconstructTrace Ŝ (chooseStepWitness sys.memFreePred Ŝ) x.S0 (sys.m * sys.Nseg)
    have hci : CommitInv (Ŝ (sys.m * sys.Nseg)) ST' := hinv (sys.m * sys.Nseg) (Nat.le_refl _)
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

/-- **CTE for the two-step VM.** If both SNARKs are knowledge-sound (and segments
are non-empty), the instantiated system is correct-trace extractable. The trace
extractor runs the two-layer straight-line extraction — `RFinal` witness, then an
`RSeg` witness per segment — and concatenates the resulting committed sub-chains.
Validity of the concatenation is `chain_flatten`. -/
theorem cte (hNseg : 0 < sys.Nseg) (h : sys.Assumptions) :
    sys.toZkVM.CTE := by
  obtain ⟨hseg, hfinal⟩ := h
  rw [ZkVM.cte_iff_knowledgeSound]
  obtain ⟨Ef, hEf⟩ := hfinal
  obtain ⟨Es, hEs⟩ := hseg
  -- The trace-extractor: extract the RFinal witness, then flatten the per-segment
  -- RSeg witnesses.
  refine ⟨⟨fun x p =>
      concatTrace sys.Nseg (Ef.extract x p).boundary
        (fun i j => (Es.extract ⟨(Ef.extract x p).boundary i,
                                 (Ef.extract x p).boundary (i + 1)⟩
                      ((Ef.extract x p).proofs i)).states j) sys.m⟩, ?_⟩
  intro x p hp
  -- Layer 1: unpack the RFinal extraction.
  obtain ⟨hb0, hbm, hbver⟩ := hEf x p hp
  set d := (Ef.extract x p).boundary with hd
  set seg := (fun i j =>
      (Es.extract ⟨d i, d (i + 1)⟩ ((Ef.extract x p).proofs i)).states j) with hs
  -- Layer 2: each segment i < m yields a valid RSeg chain.
  have h0 : ∀ i, i < sys.m → seg i 0 = d i :=
    fun i hi => (hEs _ _ (hbver i hi)).1
  have hlast : ∀ i, i < sys.m → seg i sys.Nseg = d (i + 1) :=
    fun i hi => (hEs _ _ (hbver i hi)).2.1
  -- Each committed step is certified by its extracted `MemStep` witness; the
  -- abstract trace only needs the existential projection `stepRel`.
  have hstep : ∀ i, i < sys.m → ∀ j, j < sys.Nseg →
      sys.stepRel (seg i j) (seg i (j + 1)) :=
    fun i hi j hj =>
      ⟨(Es.extract ⟨d i, d (i + 1)⟩ ((Ef.extract x p).proofs i)).steps j,
       (hEs _ _ (hbver i hi)).2.2 j hj⟩
  -- Concatenate.
  obtain ⟨e0, eT, estep⟩ :=
    chain_flatten sys.stepRel sys.Nseg sys.m hNseg d seg h0 hlast hstep
  refine ⟨?_, ?_, ?_⟩
  · show concatTrace sys.Nseg d seg sys.m 0 = x.S0
    rw [e0]; exact hb0
  · show concatTrace sys.Nseg d seg sys.m (sys.m * sys.Nseg) = x.ST
    rw [eT]; exact hbm
  · intro k hk
    exact estep k hk

/-- **Full-memory CTE** — the theorem-level bridge from `Twostep` to `Memory`,
stated as a concrete instance of the abstract `CTE`: `sys.toZkVMFull.CTE`. Under
the `cte` hypotheses plus the commitment binding assumptions, the two-step VM is
correct-trace extractable *over full-memory states* — the extractor turns every
accepting final proof into a valid full-memory trace (right boundaries, and a
genuine `∃ w, stepF …` at every step).

Proof: `cte` supplies `E`, a trace extractor for `toZkVM`, so it returns committed
traces. The trace extractor for `toZkVMFull` commits `x`'s boundaries, runs `E` on
them, and reconstructs a full-memory trace from the committed one. Correctness is
then exactly `traceValid_full` applied to `E`'s committed `TraceValid`. -/
theorem cte_full (hNseg : 0 < sys.Nseg) (h : sys.Assumptions)
    (hComplete : Complete sys.VC) (hpos : PositionBinding sys.VC)
    (hupd : UpdateBinding sys.VC) :
    sys.toZkVMFull.CTE := by
  obtain ⟨E, hE⟩ := sys.cte hNseg h
  exact ⟨fun x p =>
      let Ŝ := E ⟨toCommitted x.S0, toCommitted x.ST⟩ p
      reconstructTrace Ŝ (chooseStepWitness sys.memFreePred Ŝ) x.S0,
    fun x p hp =>
      sys.traceValid_full hComplete hpos hupd x _
        (hE ⟨toCommitted x.S0, toCommitted x.ST⟩ p hp)⟩

/-! ## Instantiating the Issue-0 step-interface contract

`Step.StepInterface`/`MemoryBridge` is the coordination scaffolding Issue 0 fixed
for the memory layer: attached to a canonical plain `ZkVM`, it asks the memory
layer to reconstruct one represented plain step from one committed step. Here the
plain `ZkVM` is `toZkVMFull` (full-memory states, `∃w. stepF`), the committed
state represents a full state via `CommitInv`, and the committed step is `stepRel`
(`∃w. stepC`). `memoryBridge` discharges `MemoryBridge` for it, showing the
Issue-1 machinery realizes the contract Issue 0 anticipated. -/

/-- The two-step VM's memory step-interface (over the full-memory `toZkVMFull`):
`CommitInv` is the representation invariant and `stepRel` the committed step. -/
def stepInterface : StepInterface sys.toZkVMFull where
  CommittedState := CommittedVMState sys.VC
  represents := fun Ŝ S => CommitInv Ŝ S
  stepCommitted := sys.stepRel

/-- **The memory bridge holds for the two-step VM.** Under the commitment binding
assumptions, `sys.stepInterface` satisfies `StepInterface.MemoryBridge`: from a
represented pre-state and a committed step, reconstruct a represented post-state
that satisfies the canonical full-memory step. This is `Memory.step_mem_extract`
(the step becomes a real `stepF`) composed with `Memory.commitInv_step` (the
representation invariant is preserved), packaged into the Issue-0 contract.

Paper: `rem:mem-inheritance` (feeding `prop:memory-extractability`). -/
theorem memoryBridge
    (hComplete : Complete sys.VC) (hpos : PositionBinding sys.VC)
    (hupd : UpdateBinding sys.VC) :
    sys.stepInterface.MemoryBridge := by
  intro Ŝ₁ Ŝ₂ S₁ hrep hstep
  obtain ⟨w, hw⟩ := hstep
  have hinv₂ : CommitInv Ŝ₂ (stepReconstruct S₁ Ŝ₂ w) :=
    commitInv_step hComplete hpos hupd sys.memFreePred S₁ Ŝ₁ Ŝ₂ w hrep hw
  exact ⟨stepReconstruct S₁ Ŝ₂ w, hinv₂,
    w, step_mem_extract hComplete hpos hupd sys.memFreePred
      S₁ (stepReconstruct S₁ Ŝ₂ w) Ŝ₁ Ŝ₂ w hrep hinv₂ hw⟩

end System
end TwoStep
end VanillaZkVM
