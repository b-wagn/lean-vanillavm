# Step-interface contract

This is the Issue 0 consistency guard shared by the memory, ISA, and bus work.
It was added as a bounded PLAN amendment accepted by Dmitry on **2026-07-29**.

The contract prevents later issues from growing unrelated predicates all called
"step." It fixes the semantic direction of the two bridge arguments while
leaving their concrete operation and witness types to their owning issues.

## Canonical interfaces

The Lean declaration `StepInterface V` has the following fields:

```text
V.step
  : V.State -> V.State -> Prop

represents
  : CommittedState -> V.State -> Prop

stepCommitted
  : CommittedState -> CommittedState -> Prop

```

`V.step` is the single canonical **plain** step predicate. Issue 3's
`ISA.stepPlain` supplies that field when it constructs the concrete `ZkVM`; it
must not create a second, disconnected top-level execution relation.

`stepCommitted` is the canonical binary relation exposed by the memory layer.
Operation-specific auxiliary witnesses and opening proofs may be carried by
internal predicates; the concrete Issue 1 instantiation uses `MemStep` and must
existentially project it when supplying this public relation.

Issue 5 separately supplies

```text
stepWithBus
  : CommittedState -> CommittedState -> BusEvidence -> Prop
```

where `BusEvidence` packages the per-step bus/chip data after the extracted buses
have been identified with one common bus. `stepWithBus` is the complete
bus-backed antecedent over that package, not the raw inner-step predicate by
itself. Keeping it out of the structure lets Issue 1 instantiate the memory
interface without inventing a dummy bus.

## Frozen bridge statements

For `I : StepInterface V`, the memory bridge is

```text
I.MemoryBridge :=
  forall committed states C1 C2 and plain state S1,
    represents C1 S1 ->
    stepCommitted C1 C2 ->
    exists S2,
      represents C2 S2 and V.step S1 S2.
```

The existential post-state is essential. A lemma that merely assumes
`represents C2 S2` and concludes `V.step S1 S2` does not establish the invariant
needed to reconstruct a whole trace; this is precisely the gap exposed by the
commitment-swap / out-of-image-commitment counterexamples.

The bus bridge is

```text
I.BusBridge stepWithBus :=
  forall C1 C2 and bus evidence b,
    stepWithBus C1 C2 b ->
    stepCommitted C1 C2.
```

The concrete extraction/unification proof may be an extract-or-break theorem
whose thin corollary constructs the common `BusEvidence` and establishes this
implication under collision resistance.

## Ownership

| Layer | Designated module | Required realization |
|---|---|---|
| Memory reconstruction | `VanillaZkVM/Memory.lean` + concrete VM module (Issue 1 / #7) | `Memory.lean` defines `CommitInv`, `committedStep`, `step_mem_extract`, `step_reconstruct`, and `trace_mem_extract`. The module owning a concrete full-memory `ZkVM` packages these as a `StepInterface` and proves `MemoryBridge`; `Twostep.lean` supplies the Issue-1 instance. |
| Plain ISA semantics | `VanillaZkVM/ISA.lean` (Issue 3 / #9) | Define `ISA.stepPlain` and use it as the concrete `ZkVM.step`. |
| Bus unification | `VanillaZkVM/Bus.lean` (Issue 5 / #11) | Define `stepWithBus` and prove `BusBridge` from extracted witnesses and bus-commitment security. |

No other module should introduce a competing public binary execution predicate.
Internal helper predicates with additional witness arguments are permitted, but
the module must expose them through this contract.

Issue 0 contains the proposition definitions rather than unproved theorem
stubs: I7 forbids `axiom`/`sorry`, and I5 forbids duplicating `ZkVM.step`.
Concrete theorem bodies remain the owning issues' deliverables.
