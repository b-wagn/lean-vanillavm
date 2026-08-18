import VanillaZkVM.Specification.Zkvm

/-!
# Step-interface contract

This module fixes the interface between the plain execution semantics, committed
memory, and the bus-deferred predicate. It is coordination scaffolding for Issues
1, 3, and 5, not a security theorem and not a new copy of the plain step
predicate.

## Main definitions
* `StepInterface` — a committed predicate and representation relation attached
  to the canonical plain predicate `ZkVM.step`.
* `StepInterface.MemoryBridge` — the proposition that one committed step can
  reconstruct one represented plain step.
* `StepInterface.BusBridge` — the proposition that a bus-deferred step implies
  the committed step after bus unification.

The concrete declarations and proofs are later-issue deliverables:
`Memory.lean`'s `step_mem_extract` / `trace_mem_extract` (Issue 1),
`ISA.stepPlain` as the concrete implementation of `ZkVM.step` (Issue 3), and
the bus-unification proof (Issue 5). See `docs/STEP_INTERFACES.md`.
-/

namespace VanillaZkVM

/-- The Lean-only coordination interface between an abstract zkVM's canonical
plain step predicate and its future committed-memory layer.

`V.step` is the unique canonical `stepPlain`; it is deliberately reused rather
than restated (I5). `represents Ŝ S` records that committed state `Ŝ` represents
plain state `S`. The public committed predicate is binary; a concrete
implementation exposes operation or opening data through an existential closure
when it instantiates this field. The bus predicate is a parameter of
`BusBridge`, so Issue 1 can instantiate this interface without inventing a
placeholder bus before Issue 5.

This interface is scaffolding, not itself a paper definition. Its fields line up
with the layers around `eq:step-bus2`, `prop:memory-extractability`, and
`lem:segment` in the pinned Vanilla zkVM paper revision. -/
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

Issue 1 proves a concrete instance using completeness, position binding, and
update binding. This formulation proves the representation relation for the
constructed second state; assuming it for both endpoint states would not suffice
for trace reconstruction.

Paper target: `prop:memory-extractability` and `rem:mem-inheritance`. -/
def MemoryBridge : Prop :=
  ∀ (Ŝ₁ Ŝ₂ : I.CommittedState) (S₁ : V.State),
    I.represents Ŝ₁ S₁ → I.stepCommitted Ŝ₁ Ŝ₂ →
      ∃ S₂ : V.State, I.represents Ŝ₂ S₂ ∧ V.step S₁ S₂

/-- The statement required from the bus layer: once the extracted bus/chip data
has been unified into evidence of type `BusEvidence`, the supplied complete
bus-backed predicate implies the canonical committed step. Keeping the bus
predicate as an argument avoids coupling the Issue-1 memory interface to an
Issue-5 witness type.

Issue 5 proves a concrete instance from inner-circuit extraction and
collision-resistance of the bus commitment.

Paper target: `lem:segment`, feeding `prop:memory-extractability`. -/
def BusBridge {BusEvidence : Type}
    (stepWithBus : I.CommittedState → I.CommittedState → BusEvidence → Prop) : Prop :=
  ∀ (Ŝ₁ Ŝ₂ : I.CommittedState) (b : BusEvidence),
    stepWithBus Ŝ₁ Ŝ₂ b → I.stepCommitted Ŝ₁ Ŝ₂

end StepInterface

end VanillaZkVM
