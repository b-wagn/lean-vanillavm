import VanillaZkVM.Specification.Zkvm

/-!
# Step-interface contract

A VM's execution appears at three levels of detail: ordinary execution over
full states, execution over memory commitments that a SNARK can check, and a
later predicate that also includes bus data. This module records how those
levels must relate, so later files do not introduce unrelated predicates all
called "step." It states the required properties; concrete VM files prove them.

## Main definitions
* `StepInterface` — a committed predicate and representation relation attached
  to the single plain predicate `ZkVM.step`.
* `StepInterface.MemoryBridge` — the proposition that one committed step can
  reconstruct one represented plain step.
* `StepInterface.BusBridge` — the proposition that a bus-deferred step implies
  the committed step after bus unification.

`TwoStep.System.memoryStepInterface` is the one instance so far, and
`TwoStep.System.memoryBridge` discharges its `MemoryBridge` from
`Memory.step_reconstruct_exact` plus the ISA correspondence theorem. Its
`ZkVM.step` is `ISA.System.stepPlain`. `BusBridge` has no instance yet; see
`docs/STEP_INTERFACES.md` for which module owns that remaining obligation.
-/

namespace VanillaZkVM

/-- The small interface connecting an abstract zkVM's plain step predicate to
its committed-memory layer.

`V.step` is the one plain step predicate, taken from the `ZkVM` itself so that
no module declares a different, unrelated execution rule (I5).
`represents Ŝ S` records that committed state `Ŝ` represents plain state `S`.
`stepCommitted` takes only its
two endpoint states. If an implementation also needs operation data or an
opening proof, it fills this field with a proposition saying that such data
exists. The bus predicate is *not* a field here but a parameter of `BusBridge`,
so a memory-only instance needs no placeholder bus.

This record only connects definitions shared by several Lean modules; it is
not a new paper definition. Its fields line up with the layers around `eq:step-bus2`,
`prop:memory-extractability`, and `lem:segment` in the pinned Vanilla zkVM paper
revision. -/
structure StepInterface (V : ZkVM) where
  CommittedState : Type
  represents : CommittedState → V.State → Prop
  stepCommitted : CommittedState → CommittedState → Prop

namespace StepInterface

variable {V : ZkVM} (I : StepInterface V)

/-- The statement required from the memory layer: if `represents C₁ S₁` and
`stepCommitted C₁ C₂`, construct `S₂` such that `represents C₂ S₂` and
`V.step S₁ S₂`.

In plain terms, if `C₁` represents a known state `S₁`, then an accepted step
from `C₁` to `C₂` must correspond to some next VM state `S₂`. The conclusion,
not an additional premise, proves both that `S₂` represents `C₂` and that
`S₁ → S₂` is a valid VM step.

Constructing `S₂` is the whole point, and the direction matters: a variant that
took `represents C₂ S₂` as a *premise* would be too weak to drive a trace
induction, because nothing would rule out a `C₂` that no plain state represents at
all. `MemorySanity` exhibits such a `C₂` when update binding is dropped.

`TwoStep.System.memoryBridge` discharges this from completeness, position binding,
and update binding, via `Memory.step_reconstruct_exact` and
`ISA.System.committedOperation_stepPlain`.

Paper target: `prop:memory-extractability` and `rem:mem-inheritance`. -/
def MemoryBridge : Prop :=
  ∀ (Ŝ₁ Ŝ₂ : I.CommittedState) (S₁ : V.State),
    I.represents Ŝ₁ S₁ → I.stepCommitted Ŝ₁ Ŝ₂ →
      ∃ S₂ : V.State, I.represents Ŝ₂ S₂ ∧ V.step S₁ S₂

/-- The statement required from the bus layer: once the extracted bus/chip data
has been unified into evidence of type `BusEvidence`, the supplied complete
bus-backed predicate implies the canonical committed step. `BusEvidence` and
`stepWithBus` are arguments rather than `StepInterface` fields, so an instance that
only has a memory layer is not forced to name a bus witness type.

No instance exists yet; the bus layer is expected to discharge this from
inner-circuit extraction and collision-resistance of the bus commitment.

Paper target: `lem:segment`, feeding `prop:memory-extractability`. -/
def BusBridge {BusEvidence : Type}
    (stepWithBus : I.CommittedState → I.CommittedState → BusEvidence → Prop) : Prop :=
  ∀ (Ŝ₁ Ŝ₂ : I.CommittedState) (b : BusEvidence),
    stepWithBus Ŝ₁ Ŝ₂ b → I.stepCommitted Ŝ₁ Ŝ₂

end StepInterface

end VanillaZkVM
