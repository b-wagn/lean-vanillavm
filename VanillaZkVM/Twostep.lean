-- This file goes at `VanillaZkVM/VanillaZkVM/TwoStep.lean`.

import VanillaZkVM.Crypto

/-!
# A minimal "two-step" zkVM (deliberate deviation from the full architecture)

This is a stripped-down system that keeps the two features which make the
security argument non-trivial — composing straight-line extraction across SNARK
layers, and committed-memory states — while dropping the bus, the four inner
circuits, the chips, and the binary `convert`/`combine`/`embed` tower.

* Segment layer `R_seg`: a chain of `Nseg` committed steps `Sin → Sout` under an
  assumed committed step predicate `stepC` (`φ̂_step`). Operations are *not*
  deferred to a bus.
* Final layer `R_final`: a single SNARK that merges `m` segment proofs whose
  boundary states chain `S0 → ST`.

## What is (deliberately) simplified

The correct-trace-extractability conclusion below is stated over
**committed-memory** states: it produces a valid *segmented* execution of
`stepC`. Two things are therefore postponed to later increments, both built on
top of this exact theorem:

1. **Full-memory reconstruction.** Turning the committed trace into a full-memory
   trace is where `Com_mem`'s position- and punctured-binding is actually used (the
   memory-extractability proposition). Here `Com_mem` is a declared component but
   its binding is not yet consumed.
2. **Flattening.** We conclude "each of the `m` segments is a valid `R_seg`
   chain" rather than flattening the `m·Nseg` steps into one `Fin (T+1)`
   sequence; flattening is a separate, purely combinatorial step.

Neither choice is discarded on upgrade: the segment/final relations and the
two-layer extraction proof are reused verbatim.
-/

namespace VanillaZkVM
namespace TwoStep

/-! ## Statements and witnesses -/

/-- Statement of the segment relation: the committed boundary states. -/
structure SegStmt (VC : VectorCommitment) where
  Sin : CommittedVMState VC
  Sout : CommittedVMState VC

/-- Witness of the segment relation: the `Nseg + 1` intermediate committed
states. (No memory-opening witnesses yet: see the module header.) -/
structure SegWitness (VC : VectorCommitment) (Nseg : ℕ) where
  states : Fin (Nseg + 1) → CommittedVMState VC

/-- Statement of the final relation: the committed boundary states of the whole
execution. -/
structure FinalStmt (VC : VectorCommitment) where
  S0 : CommittedVMState VC
  ST : CommittedVMState VC

/-- Witness of the final relation: `m` segment proofs and the `m + 1` boundary
states they connect. -/
structure FinalWitness (VC : VectorCommitment) (m : ℕ) (SegProof : Type) where
  boundary : Fin (m + 1) → CommittedVMState VC
  proofs : Fin m → SegProof

/-! ## The toy system -/

/-- The toy system: an assumed committed step predicate, a memory commitment
scheme, and the two proof types with their prove/verify algorithms. The
relations and argument systems are derived below. -/
structure System where
  VC : VectorCommitment
  Nseg : ℕ
  m : ℕ
  /-- Committed step predicate `φ̂_step` (assumed to exist). -/
  stepC : CommittedVMState VC → CommittedVMState VC → Prop
  SegProof : Type
  segProve : SegStmt VC → SegWitness VC Nseg → SegProof
  segVerify : SegStmt VC → SegProof → Prop
  FinalProof : Type
  finalProve : FinalStmt VC → FinalWitness VC m SegProof → FinalProof
  finalVerify : FinalStmt VC → FinalProof → Prop

namespace System

variable (sys : System)

/-- Segment relation `R_seg`: a chain of `Nseg` committed steps from `Sin` to
`Sout`. -/
def RSeg : Relation where
  Stmt := SegStmt sys.VC
  Wit := SegWitness sys.VC sys.Nseg
  rel := fun st w =>
    w.states 0 = st.Sin ∧
    w.states (Fin.last sys.Nseg) = st.Sout ∧
    ∀ i : Fin sys.Nseg, sys.stepC (w.states i.castSucc) (w.states i.succ)

/-- The segment argument system `Π_seg`. -/
def ASSeg : ArgumentSystem sys.RSeg where
  Proof := sys.SegProof
  prove := sys.segProve
  verify := sys.segVerify

/-- Final relation `R_final`: `m` segment proofs, each accepted by `Π_seg`, whose
boundary states chain from `S0` to `ST`. -/
def RFinal : Relation where
  Stmt := FinalStmt sys.VC
  Wit := FinalWitness sys.VC sys.m sys.SegProof
  rel := fun st w =>
    w.boundary 0 = st.S0 ∧
    w.boundary (Fin.last sys.m) = st.ST ∧
    ∀ i : Fin sys.m,
      sys.segVerify ⟨w.boundary i.castSucc, w.boundary i.succ⟩ (w.proofs i)

/-- The final argument system `Π_final`. -/
def ASFinal : ArgumentSystem sys.RFinal where
  Proof := sys.FinalProof
  prove := sys.finalProve
  verify := sys.finalVerify

end System

/-! ## Correct-trace extractability (committed-memory target) -/

/-- **Toy CTE.** If both SNARKs are knowledge-sound, any accepting final proof
yields a valid segmented committed-memory execution: boundary states from `S0`
to `ST`, each adjacent pair certified by a genuine `R_seg` witness (hence by a
chain of `Nseg` committed steps).

The proof is a two-layer straight-line extraction: extract the `R_final` witness
(the `m` segment proofs and boundary states) from `pf`, then extract an `R_seg`
witness from each segment proof. No probabilities, no bus, no memory
reconstruction. -/
theorem toy_cte (sys : System)
    (hseg : KnowledgeSound sys.ASSeg)
    (hfinal : KnowledgeSound sys.ASFinal)
    (st : FinalStmt sys.VC) (pf : sys.FinalProof)
    (hpf : sys.finalVerify st pf) :
    ∃ d : Fin (sys.m + 1) → CommittedVMState sys.VC,
      d 0 = st.S0 ∧ d (Fin.last sys.m) = st.ST ∧
      ∀ i : Fin sys.m,
        ∃ ws : SegWitness sys.VC sys.Nseg,
          sys.RSeg.rel ⟨d i.castSucc, d i.succ⟩ ws := by
  obtain ⟨Efinal, hEfinal⟩ := hfinal
  obtain ⟨Eseg, hEseg⟩ := hseg
  -- Layer 1: extract the R_final witness from the accepting final proof.
  have hw := hEfinal st pf hpf
  set w := Efinal.extract st pf with hwdef
  obtain ⟨hb0, hblast, hverify⟩ := hw
  refine ⟨w.boundary, hb0, hblast, ?_⟩
  intro i
  -- Layer 2: extract an R_seg witness for segment i from its (accepted) proof.
  exact ⟨Eseg.extract ⟨w.boundary i.castSucc, w.boundary i.succ⟩ (w.proofs i),
         hEseg ⟨w.boundary i.castSucc, w.boundary i.succ⟩ (w.proofs i) (hverify i)⟩

end TwoStep
end VanillaZkVM
