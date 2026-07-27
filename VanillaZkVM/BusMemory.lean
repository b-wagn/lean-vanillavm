import VanillaZkVM.Bus
import VanillaZkVM.MemoryTrace

/-!
# Bus-to-full-memory composition

This file composes the two reductions that were previously separate:

1. `Bus.System.segment_extract` turns an accepting segment proof into a
   committed trace whose every leaf satisfies `System.step`;
2. `reconstructTrace_from_initial` turns those committed steps into a
   full-memory trace while constructing every later commitment invariant.

There is no free-standing `BusRefinesStep` hypothesis. `Bus.System.stepBus` is
definitionally a `Memory.stepC` using the descriptor and core semantics stored
in the extracted `StepAux`. The remaining semantic trust boundary is explicit:
the individual `System.operation` predicates remain abstract until a concrete
VanillaVM program/ISA instantiates them.
-/

namespace VanillaZkVM
namespace Bus
namespace System

variable (sys : System)

/-- The memory descriptor retained by the extracted auxiliary witness at step
`k`. -/
def segmentDescriptor
    (w : InnerStepWitness sys.VC sys.H sys.StepAux) (k : ℕ) :
    MemStep sys.VC :=
  sys.memStep (w.stepAux k)

/-- The PC/register/program predicate selected by the extracted bus and
auxiliary witness at step `k`. -/
def segmentCoreStep
    (w : InnerStepWitness sys.VC sys.H sys.StepAux) (k : ℕ) :
    MemFreePredicate :=
  sys.coreStep w.bus (w.stepAux k)

/-- Full-memory validity of the trace deterministically reconstructed from a
segment witness. -/
def MemoryTraceValid
    [DecidableEq sys.VC.Index] [DecidableEq sys.VC.Value]
    [DecidableEq sys.VC.Com]
    (w : InnerStepWitness sys.VC sys.H sys.StepAux)
    (initial : FullVMState sys.VC) : Prop :=
  let trace :=
    reconstructTrace initial w.states (sys.segmentDescriptor w)
  trace 0 = initial ∧
  (∀ k, k ≤ sys.Nseg → CommitInv (w.states k) (trace k)) ∧
  ∀ k, k < sys.Nseg →
    stepF (sys.segmentCoreStep w k)
      (trace k) (trace (k + 1)) (sys.segmentDescriptor w k)

/-- A semantic segment witness reconstructs to a full-memory trace, provided
its public initial boundary honestly commits to the supplied initial full
state. In particular, it *constructs* the post-memory and its `CommitInv`; it
does not assume an invariant for the segment's post-state.

This is the first direct composition point between `Bus.lean` and
`MemoryTrace.lean`. -/
theorem segment_reconstruct_memory
    [DecidableEq sys.VC.Index] [DecidableEq sys.VC.Value]
    [DecidableEq sys.VC.Com]
    (hComplete : Complete sys.VC) (hpos : PositionBinding sys.VC)
    (hupd : UpdateBinding sys.VC)
    (statement : SegmentStmt sys.VC)
    (witness : InnerStepWitness sys.VC sys.H sys.StepAux)
    (hWitness : sys.RSegmentTrace.rel statement witness)
    (initial : FullVMState sys.VC)
    (hInitial : CommitInv statement.Sin initial) :
    sys.MemoryTraceValid witness initial := by
  obtain ⟨hStateZero, _, hSteps⟩ := hWitness
  have hInitial' : CommitInv (witness.states 0) initial := by
    rw [hStateZero]
    exact hInitial
  have hCommittedSteps :
      ∀ k, k < sys.Nseg →
        stepC (sys.segmentCoreStep witness k)
          (witness.states k) (witness.states (k + 1))
          (sys.segmentDescriptor witness k) := by
    intro k hk
    exact (hSteps k hk).1
  exact reconstructTrace_from_initial hComplete hpos hupd
      (sys.segmentCoreStep witness) sys.Nseg initial
      witness.states (sys.segmentDescriptor witness)
      hInitial' hCommittedSteps

/-- End-to-end segment theorem: an accepting segment proof first yields the
single bus-unified semantic witness, then reconstructs a valid full-memory
trace. The returned witness makes the reduction inspectable rather than hiding
it behind a bare implication. -/
theorem accepting_segment_reconstructs_memory
    [DecidableEq sys.VC.Index] [DecidableEq sys.VC.Value]
    [DecidableEq sys.VC.Com]
    (hAssumptions : sys.Assumptions)
    (hComplete : Complete sys.VC) (hpos : PositionBinding sys.VC)
    (hupd : UpdateBinding sys.VC)
    (statement : SegmentStmt sys.VC) (proof : sys.SegmentProof)
    (hAccept : sys.segmentVerify statement proof)
    (initial : FullVMState sys.VC)
    (hInitial : CommitInv statement.Sin initial) :
    ∃ witness : InnerStepWitness sys.VC sys.H sys.StepAux,
      sys.RSegmentTrace.rel statement witness ∧
      sys.MemoryTraceValid witness initial := by
  obtain ⟨extractor, hExtractor⟩ := sys.segment_extract hAssumptions
  let witness := extractor.extract statement proof
  have hWitness : sys.RSegmentTrace.rel statement witness :=
    hExtractor statement proof hAccept
  have hTrace :=
    sys.segment_reconstruct_memory hComplete hpos hupd
      statement witness hWitness initial hInitial
  exact ⟨witness, hWitness, hTrace⟩

end System
end Bus
end VanillaZkVM
