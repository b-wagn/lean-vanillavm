import VanillaZkVM.Memory

/-!
# A minimal "two-step" zkVM, instantiating the abstract system

A stripped-down system that keeps the two features that make the security
argument non-trivial — composing straight-line extraction across SNARK layers,
and committed-memory states — while dropping the bus, the four inner circuits,
the chips, and the binary `convert`/`combine`/`embed` tower.

* Segment layer `RSeg`: a chain of `Nseg` committed steps `Sin → Sout` under the
  classified committed step predicate `stepC` (from `Memory`). Each step carries
  its explicit `MemStep` descriptor, including the opening used by a read/write.
  Operations are not deferred to a bus.
* Final layer `RFinal`: a single SNARK merging `m` segment proofs whose boundary
  states chain `S0 → ST`.

We then instantiate the abstract `ZkVM` (`State` = committed states,
`T = m * Nseg`) and prove `CTE`, via the equivalence with `KnowledgeSound ASstar`
plus a two-layer extraction. The committed trace is produced with `concatTrace`;
its validity rests on `chain_flatten`.

Simplifications carried over: the CTE target is a committed-memory trace whose
binary step is the existential projection `stepRel` of the classified `stepC` —
the per-step `MemStep` descriptors are retained in the segment witnesses (where
`Memory.step_mem_extract` consumes `Com_mem`'s binding), but full-memory
reconstruction and folding those descriptors through the flattened trace are the
next increment. Traces are `ℕ`-indexed with `< bound` conditions (uniform with
`Rstar`, and it makes concatenation pure `ℕ`-arithmetic).
-/

namespace VanillaZkVM
namespace TwoStep

/-! ## Statements and witnesses -/

/-- Segment statement: the committed boundary states. -/
structure SegStmt (VC : VectorCommitment) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC

/-- Segment witness: the intermediate committed states and one explicit
`MemStep` descriptor per transition, both `ℕ`-indexed (only the first `Nseg + 1`
states and `Nseg` steps matter). Read/write descriptors carry the openings that
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

/-! ## The toy system -/

/-- The toy system: an assumed committed step predicate, a memory commitment
scheme, and the two layers' proof types with their verifiers. -/
structure System where
  VC : VectorCommitment
  Nseg : ℕ
  m : ℕ
  /-- Memory-free register/program-counter part of each classified step; the full
  committed step is `stepC regPart` (from `Memory`). -/
  regPart : RegPart
  SegProof : Type
  segVerify : SegStmt VC → SegProof → Prop
  FinalProof : Type
  finalVerify : FinalStmt VC → FinalProof → Prop

namespace System

variable (sys : System)

/-- The binary committed-step relation the abstract ZkVM sees: a step holds iff
some `MemStep` descriptor certifies it under `stepC sys.regPart`. The descriptors
themselves are retained in `SegWitness.steps`, where memory extractability
(`Memory.step_mem_extract`) consumes them; the flattened abstract trace only
needs this binary relation. -/
def stepRel (Ŝ₁ Ŝ₂ : CommittedVMState sys.VC) : Prop :=
  ∃ w : MemStep sys.VC, stepC sys.regPart Ŝ₁ Ŝ₂ w

/-- Segment relation `RSeg`: a chain of `Nseg` committed steps from `Sin` to
`Sout`, each certified by its explicit `MemStep` descriptor. -/
def RSeg : Relation where
  Stmt := SegStmt sys.VC
  Wit := SegWitness sys.VC
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states sys.Nseg = st.Sout ∧
    ∀ j, j < sys.Nseg →
      stepC sys.regPart (w.states j) (w.states (j + 1)) (w.steps j)

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

/-- **CTE for the two-step VM.** If both SNARKs are knowledge-sound (and segments
are non-empty), the instantiated system is correct-trace extractable. The trace
extractor runs the two-layer straight-line extraction — `RFinal` witness, then an
`RSeg` witness per segment — and concatenates the resulting committed sub-chains.
Validity of the concatenation is `chain_flatten`. -/
theorem cte (hNseg : 0 < sys.Nseg)
    (hseg : KnowledgeSound sys.ASSeg)
    (hfinal : KnowledgeSound sys.ASFinal) :
    sys.toZkVM.CTE := by
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
  -- Each committed step is certified by its extracted `MemStep` descriptor; the
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

end System
end TwoStep
end VanillaZkVM
