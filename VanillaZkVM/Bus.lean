import VanillaZkVM.Zkvm

/-!
# Bus-delegated segment extraction

This file models the leaf layer of the Vanilla zkVM proof architecture:

* `RInnerStep` proves a segment of committed steps against a bus commitment.
* `RInnerKeccak`, `RInnerPoseidon`, and `RInnerRange` prove the three predicates
  delegated to that bus.
* `RSegment` verifies the four inner proofs under one public bus commitment.

The theorem `segment_extract` formalizes the bus-unification step in the
security proof. Straight-line extraction may return four buses, but each hashes
to the bus commitment carried by the segment witness. Collision-resistance
therefore makes all four buses equal, so their predicates combine into a single
valid segment trace.

As in the rest of the development, cryptographic security is perfect and
probability-free. The bus contents and operation predicates remain abstract;
only the proposition-level extraction argument is modeled here.
-/

namespace VanillaZkVM
namespace Bus

/-! ## Statements and witnesses -/

/-- Public input to `inner-step`: committed segment boundaries and the shared
bus commitment. -/
structure InnerStepStmt (VC : VectorCommitment) (H : HashCommitment) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC
  busCom : H.Digest

/-- Witness extracted from `inner-step`: one bus, the committed state chain,
and the explicit per-step auxiliary witnesses (including memory openings). -/
structure InnerStepWitness (VC : VectorCommitment) (H : HashCommitment)
    (StepAux : Type) where
  bus : H.Domain
  states : ℕ → CommittedVMState VC
  stepAux : ℕ → StepAux

/-- Public input to `segment`: the committed boundary states. -/
structure SegmentStmt (VC : VectorCommitment) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC

/-- The `segment` witness: a shared bus commitment and one proof for each inner
relation. -/
structure SegmentWitness (H : HashCommitment) (InnerStepProof InnerKeccakProof
    InnerPoseidonProof InnerRangeProof : Type) where
  busCom : H.Digest
  stepProof : InnerStepProof
  keccakProof : InnerKeccakProof
  poseidonProof : InnerPoseidonProof
  rangeProof : InnerRangeProof

/-! ## The bus-delegated segment system -/

/-- The leaf and segment layers needed for bus delegation. `stepBus` is the
committed-memory predicate `φ̂_step,bus`; the other three predicates validate all
entries of their type in the bus. -/
structure System where
  VC : VectorCommitment
  H : HashCommitment
  Nseg : ℕ
  StepAux : Type
  stepBus : CommittedVMState VC → CommittedVMState VC → H.Domain → StepAux → Prop
  keccak : H.Domain → Prop
  poseidon : H.Domain → Prop
  range : H.Domain → Prop
  InnerStepProof : Type
  innerStepVerify : InnerStepStmt VC H → InnerStepProof → Prop
  InnerKeccakProof : Type
  innerKeccakVerify : H.Digest → InnerKeccakProof → Prop
  InnerPoseidonProof : Type
  innerPoseidonVerify : H.Digest → InnerPoseidonProof → Prop
  InnerRangeProof : Type
  innerRangeVerify : H.Digest → InnerRangeProof → Prop
  SegmentProof : Type
  segmentVerify : SegmentStmt VC → SegmentProof → Prop

namespace System

variable (sys : System)

/-! ## Inner and segment relations -/

/-- `R_(0,step)`: a committed `Nseg`-step chain whose deferred operations refer
to a bus hashing to the public bus commitment. -/
def RInnerStep : Relation where
  Stmt := InnerStepStmt sys.VC sys.H
  Wit := InnerStepWitness sys.VC sys.H sys.StepAux
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states sys.Nseg = st.Sout ∧
    (∀ j, j < sys.Nseg →
      sys.stepBus (w.states j) (w.states (j + 1)) w.bus (w.stepAux j)) ∧
    st.busCom = sys.H.hash w.bus

/-- The `inner-step` argument system `Π_(0,step)`. -/
def ASInnerStep : ArgumentSystem sys.RInnerStep where
  Proof := sys.InnerStepProof
  verify := sys.innerStepVerify

/-- An inner chip relation: the extracted bus satisfies `pred` and hashes to
the public bus commitment. -/
def RInnerChip (pred : sys.H.Domain → Prop) : Relation where
  Stmt := sys.H.Digest
  Wit := sys.H.Domain
  rel := fun busCom bus => pred bus ∧ busCom = sys.H.hash bus

/-- `R_(0,keccak)`: every Keccak entry in the committed bus is valid. -/
def RInnerKeccak : Relation := sys.RInnerChip sys.keccak

/-- `R_(0,poseidon)`: every Poseidon entry in the committed bus is valid. -/
def RInnerPoseidon : Relation := sys.RInnerChip sys.poseidon

/-- `R_(0,range)`: every range-check entry in the committed bus is valid. -/
def RInnerRange : Relation := sys.RInnerChip sys.range

/-- The `inner-keccak` argument system `Π_(0,keccak)`. -/
def ASInnerKeccak : ArgumentSystem sys.RInnerKeccak where
  Proof := sys.InnerKeccakProof
  verify := sys.innerKeccakVerify

/-- The `inner-poseidon` argument system `Π_(0,poseidon)`. -/
def ASInnerPoseidon : ArgumentSystem sys.RInnerPoseidon where
  Proof := sys.InnerPoseidonProof
  verify := sys.innerPoseidonVerify

/-- The `inner-range` argument system `Π_(0,range)`. -/
def ASInnerRange : ArgumentSystem sys.RInnerRange where
  Proof := sys.InnerRangeProof
  verify := sys.innerRangeVerify

/-- `R_1`: four accepted inner proofs tied together by one bus commitment. -/
def RSegment : Relation where
  Stmt := SegmentStmt sys.VC
  Wit := SegmentWitness sys.H sys.InnerStepProof sys.InnerKeccakProof
    sys.InnerPoseidonProof sys.InnerRangeProof
  rel := fun st w =>
    sys.innerStepVerify ⟨st.Sin, st.Sout, w.busCom⟩ w.stepProof ∧
    sys.innerKeccakVerify w.busCom w.keccakProof ∧
    sys.innerPoseidonVerify w.busCom w.poseidonProof ∧
    sys.innerRangeVerify w.busCom w.rangeProof

/-- The `segment` argument system `Π_1`. -/
def ASSegment : ArgumentSystem sys.RSegment where
  Proof := sys.SegmentProof
  verify := sys.segmentVerify

/-! ## Semantic segment relation -/

/-- The complete committed step predicate: inline step checking together with
the three predicates delegated to the common bus. -/
def step (S₁ S₂ : CommittedVMState sys.VC) (bus : sys.H.Domain)
    (aux : sys.StepAux) : Prop :=
  sys.stepBus S₁ S₂ bus aux ∧
  sys.keccak bus ∧ sys.poseidon bus ∧ sys.range bus

/-- The semantic segment relation obtained after extracting and unifying the
four inner buses. -/
def RSegmentTrace : Relation where
  Stmt := SegmentStmt sys.VC
  Wit := InnerStepWitness sys.VC sys.H sys.StepAux
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states sys.Nseg = st.Sout ∧
    ∀ j, j < sys.Nseg →
      sys.step (w.states j) (w.states (j + 1)) w.bus (w.stepAux j)

/-- The segment verifier, viewed as an argument system for the semantic segment
relation rather than the proof-carrying relation `RSegment`. -/
def ASSegmentTrace : ArgumentSystem sys.RSegmentTrace where
  Proof := sys.SegmentProof
  verify := sys.segmentVerify

/-! ## Segment extraction -/

/-- **Trust base for the bus-delegated segment layer** — the single surface
collecting every unproven cryptographic assumption `segment_extract` relies on.
Every field is an idealized/heuristic property (perfect knowledge soundness /
collision resistance; see `Crypto.lean`). Bundling them here makes the layer's
entire trust base one greppable object instead of a scattered hypothesis list.
Note this system *does* use a bus, so collision-resistance appears (contrast
`TwoStep.System.Assumptions`, which has neither a bus nor inner circuits). -/
structure Assumptions (sys : System) : Prop where
  /-- Collision-resistance of the bus hash commitment `Com_bus`. -/
  busCR : CollisionResistant sys.H
  /-- Knowledge soundness of the `inner-step` circuit `Π_(0,step)`. -/
  ksInnerStep : KnowledgeSound sys.ASInnerStep
  /-- Knowledge soundness of the `inner-keccak` circuit `Π_(0,keccak)`. -/
  ksInnerKeccak : KnowledgeSound sys.ASInnerKeccak
  /-- Knowledge soundness of the `inner-poseidon` circuit `Π_(0,poseidon)`. -/
  ksInnerPoseidon : KnowledgeSound sys.ASInnerPoseidon
  /-- Knowledge soundness of the `inner-range` circuit `Π_(0,range)`. -/
  ksInnerRange : KnowledgeSound sys.ASInnerRange
  /-- Knowledge soundness of the `segment` SNARK `Π_1`. -/
  ksSegment : KnowledgeSound sys.ASSegment

/-- **Segment extraction.** Knowledge-soundness of the segment and four inner
argument systems, together with collision-resistance of the bus commitment,
makes the segment verifier knowledge-sound for a trace satisfying the complete
bus-delegated step predicate.

The extractor first obtains the four inner proofs from `RSegment`, then extracts
their witnesses. All four extracted buses hash to the same `busCom`; `hbus`
identifies them, allowing the three chip predicates to be transported to the
`inner-step` bus. -/
theorem segment_extract (h : sys.Assumptions) :
    KnowledgeSound sys.ASSegmentTrace := by
  obtain ⟨hbus, hstep, hkeccak, hposeidon, hrange, hsegment⟩ := h
  obtain ⟨E₁, hE₁⟩ := hsegment
  obtain ⟨Estep, hEstep⟩ := hstep
  obtain ⟨Ekeccak, hEkeccak⟩ := hkeccak
  obtain ⟨Eposeidon, hEposeidon⟩ := hposeidon
  obtain ⟨Erange, hErange⟩ := hrange
  let E : Extractor sys.RSegmentTrace sys.ASSegmentTrace :=
    ⟨fun x p =>
      let w₁ := E₁.extract x p
      Estep.extract ⟨x.Sin, x.Sout, w₁.busCom⟩ w₁.stepProof⟩
  refine ⟨E, ?_⟩
  intro x p hp
  let w₁ := E₁.extract x p
  have hw₁ : sys.RSegment.rel x w₁ := hE₁ x p hp
  obtain ⟨hvstep, hvkeccak, hvposeidon, hvrange⟩ := hw₁
  let stepStmt : InnerStepStmt sys.VC sys.H := ⟨x.Sin, x.Sout, w₁.busCom⟩
  let wstep := Estep.extract stepStmt w₁.stepProof
  have hwstep : sys.RInnerStep.rel stepStmt wstep :=
    hEstep stepStmt w₁.stepProof hvstep
  obtain ⟨hs₀, hsN, hsstep, hsCom⟩ := hwstep
  let bkeccak := Ekeccak.extract w₁.busCom w₁.keccakProof
  have hbkeccak : sys.RInnerKeccak.rel w₁.busCom bkeccak :=
    hEkeccak w₁.busCom w₁.keccakProof hvkeccak
  obtain ⟨hkeccakPred, hkeccakCom⟩ := hbkeccak
  let bposeidon := Eposeidon.extract w₁.busCom w₁.poseidonProof
  have hbposeidon : sys.RInnerPoseidon.rel w₁.busCom bposeidon :=
    hEposeidon w₁.busCom w₁.poseidonProof hvposeidon
  obtain ⟨hposeidonPred, hposeidonCom⟩ := hbposeidon
  let brange := Erange.extract w₁.busCom w₁.rangeProof
  have hbrange : sys.RInnerRange.rel w₁.busCom brange :=
    hErange w₁.busCom w₁.rangeProof hvrange
  obtain ⟨hrangePred, hrangeCom⟩ := hbrange
  have hbusKeccak : wstep.bus = bkeccak :=
    hbus wstep.bus bkeccak (hsCom.symm.trans hkeccakCom)
  have hbusPoseidon : wstep.bus = bposeidon :=
    hbus wstep.bus bposeidon (hsCom.symm.trans hposeidonCom)
  have hbusRange : wstep.bus = brange :=
    hbus wstep.bus brange (hsCom.symm.trans hrangeCom)
  have hkeccak' : sys.keccak wstep.bus := by
    rw [hbusKeccak]
    exact hkeccakPred
  have hposeidon' : sys.poseidon wstep.bus := by
    rw [hbusPoseidon]
    exact hposeidonPred
  have hrange' : sys.range wstep.bus := by
    rw [hbusRange]
    exact hrangePred
  change sys.RSegmentTrace.rel x wstep
  refine ⟨hs₀, hsN, ?_⟩
  intro j hj
  exact ⟨hsstep j hj, hkeccak', hposeidon', hrange'⟩

end System
end Bus
end VanillaZkVM
