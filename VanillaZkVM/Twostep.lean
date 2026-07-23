import VanillaZkVM.Zkvm

/-!
# A minimal "two-step" zkVM, instantiating the abstract system

A stripped-down system that keeps the two features that make the security
argument non-trivial — composing straight-line extraction across SNARK layers,
and committed-memory states — while dropping the bus, the four inner circuits,
the chips, and the binary `convert`/`combine`/`embed` tower.

* Segment layer `RSeg`: a chain of `Nseg` committed steps `Sin → Sout` under an
  assumed committed step predicate `stepC`. Operations are not deferred to a bus.
* Final layer `RFinal`: a single SNARK merging `m` segment proofs whose boundary
  states chain `S0 → ST`.

We then instantiate the abstract `ZkVM` (`State` = committed states,
`T = m * Nseg`) and prove `CTE`, via the equivalence with `KnowledgeSound ASstar`
plus a two-layer extraction. The committed trace is produced with `concatTrace`;
its validity rests on `chain_flatten`.

Simplifications carried over: the CTE target is a committed-memory trace (so
`Com_mem`'s binding is a declared component but not yet consumed — full-memory
reconstruction is the next increment), and traces are `ℕ`-indexed with `< bound`
conditions (uniform with `Rstar`, and it makes concatenation pure `ℕ`-arithmetic).
-/

namespace VanillaZkVM
namespace TwoStep

/-! ## Statements and witnesses -/

/-- Segment statement: the committed boundary states. -/
structure SegStmt (VC : VectorCommitment) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC

/-- Segment witness: the intermediate committed states, `ℕ`-indexed (only the
first `Nseg + 1` matter). -/
structure SegWitness (VC : VectorCommitment) where
  states : ℕ → CommittedVMState VC

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
  /-- Committed step predicate `φ̂_step` (assumed to exist). -/
  stepC : CommittedVMState VC → CommittedVMState VC → Prop
  SegProof : Type
  segVerify : SegStmt VC → SegProof → Prop
  FinalProof : Type
  finalVerify : FinalStmt VC → FinalProof → Prop

namespace System

variable (sys : System)

/-- Segment relation `RSeg`: a chain of `Nseg` committed steps from `Sin` to
`Sout`. -/
def RSeg : Relation where
  Stmt := SegStmt sys.VC
  Wit := SegWitness sys.VC
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states sys.Nseg = st.Sout ∧
    ∀ j, j < sys.Nseg → sys.stepC (w.states j) (w.states (j + 1))

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
  step := sys.stepC
  T := sys.m * sys.Nseg
  Stmt := FinalStmt sys.VC
  initial := FinalStmt.S0
  terminal := FinalStmt.ST
  Proof := sys.FinalProof
  verify := sys.finalVerify

/-- **Trust base for the two-step zkVM** — the single surface collecting the
unproven assumptions `cte` relies on. This toy system uses no bus, so its trust
base is exactly the two SNARKs' knowledge soundness: no collision-resistance and
no inner circuits (contrast `Bus.System.Assumptions`). Both fields are
idealized/heuristic; see `Crypto.lean`. The well-formedness side condition
`0 < Nseg` is *not* part of the trust base and stays a separate argument to
`cte`. -/
structure Assumptions (sys : System) : Prop where
  /-- Knowledge soundness of the segment SNARK `Π_seg`. -/
  ksSeg : KnowledgeSound sys.ASSeg
  /-- Knowledge soundness of the final merging SNARK `Π_final`. -/
  ksFinal : KnowledgeSound sys.ASFinal

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
  have hstep : ∀ i, i < sys.m → ∀ j, j < sys.Nseg →
      sys.stepC (seg i j) (seg i (j + 1)) :=
    fun i hi j hj => (hEs _ _ (hbver i hi)).2.2 j hj
  -- Concatenate.
  obtain ⟨e0, eT, estep⟩ :=
    chain_flatten sys.stepC sys.Nseg sys.m hNseg d seg h0 hlast hstep
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
