# Issue 1 — memory reconstruction

This note gives a human-readable overview of the memory-reconstruction
formalization. It is intended to guide review of the definitions and theorem
statements; the line-by-line paper correspondence remains in
[`CORRESPONDENCE.md`](CORRESPONDENCE.md), and the ordinary mathematical
statements remain in [`../VanillaZkVM/math-companion.md`](../VanillaZkVM/math-companion.md).

## `Crypto.lean`

The goal of the Issue 1 additions is to define `UpdateBinding`. If `m'` is `m`
updated at one address, and the same opening proof verifies the old value
against `commit m` and the new value against a candidate root `C'`, then `C'`
must equal `commit m'`. This prevents accepted post-state commitments that do
not represent the correctly updated memory.

- **Position binding.** If two openings at the same address verify against the
  same commitment, then they reveal the same value.
- **Update binding.** Consider memories `m` and `m'`, a fixed address `addr`,
  and a new value `x`. Suppose that `m'` equals `m` everywhere except at
  `addr`, where its value is `x`. If the same opening proof verifies the old
  value against `commit m` and `x` against a candidate updated commitment
  `C'`, then `C' = commit m'`.

## `Memory.lean`

The goal of this file is to prove `trace_mem_extract`. Assuming completeness,
position binding, and update binding, a committed trace with valid
committed-memory steps can be reconstructed from a known full initial state
into a full-memory trace. Every reconstructed state corresponds to its
committed state under `CommitInv`, and every reconstructed transition satisfies
the corresponding full-memory predicate `FullMemory.step`. The private theorem
`reconstructed_step_full` provides the one-step semantic component, while the
public theorem `step_reconstruct` packages the constructive one-step bridge.

- `FullVMState` represents states containing the complete memory map.
- `CommitInv` relates a full state to a committed state: their program counters
  and registers agree, and the committed state's memory field is the commitment
  to the full state's memory.
- `MemStep` makes the memory behavior implicit in an instruction explicit:
  - a read contains an address, a value, and an opening proof;
  - a write contains an address, the new value, the old value, and an opening
    proof;
  - other instructions carry no additional memory data.
- `CommittedMemory.read` and `CommittedMemory.write` describe correct reads and writes between committed
  states.
- `FullMemory.read` and `FullMemory.write` describe the corresponding operations between
  full-memory states.
- `CommittedMemory.step` is the committed-memory transition, case-split over
  reads, writes, and other instructions.
- `committedStep` hides the `MemStep` witness existentially and is the binary
  committed relation exposed through `StepInterface`.
- `FullMemory.step` is the corresponding full-memory transition, case-split over
  the same witness.
- `step_mem_extract` assumes that both full endpoint states and both commitment
  invariants are already available. It proves that a `CommittedMemory.step` also
  satisfies `FullMemory.step`. Because it assumes the post-state invariant, it is a
  conditional refinement theorem rather than the induction step used to
  reconstruct a trace.
- `commit_update` shows that a candidate post-state commitment is the commitment
  to the point-updated memory. It uses the old and new accepted openings,
  position binding, and update binding.
- `commitInv_write` proves that a reconstructed correct write preserves
  `CommitInv` from the pre-state to the post-state.
- `stepReconstruct` constructs the full post-state from a full pre-state, a
  committed candidate post-state, and a `MemStep` witness.
- `reconstructTrace` applies `stepReconstruct` inductively to reconstruct the
  complete full-memory trace from the committed states and initial full state.
- `commitInv_step` proves that the reconstructed post-state remains related to
  the corresponding committed post-state by `CommitInv`.
- `reconstructed_step_full` proves that the reconstructed post-state satisfies
  the full-memory semantics of the same `MemStep` witness.
- `step_reconstruct` proves the constructive one-step bridge: from
  `CommitInv Ŝ₁ S₁` and a committed transition from `Ŝ₁` to `Ŝ₂`, it
  constructs a full state `S₂` and `MemStep` witness `w` such that both
  `CommitInv Ŝ₂ S₂` and `FullMemory.step S₁ S₂ w` hold.
- `trace_mem_extract` folds the preceding result across a sequence of committed
  states. The reconstructed states satisfy both the commitment invariant and
  the full-memory transition relation at every index in the trace.

## `MemorySanity.lean`

The goal of this file is to show that the memory assumptions are coherent,
non-vacuous, and necessary.

- `exactVC` is a positive vector-commitment model satisfying completeness,
  position binding, and update binding. The file also checks a genuine changed
  write, rather than only a no-op transition.
- `appendBitVC` is a negative model satisfying completeness, position binding,
  and a private version of the legacy punctured non-equivocation condition, but
  not update binding. It accepts a malformed post-state commitment that is not
  the commitment of any full memory.
- `appendBitBreak` is a concrete `UpdateBindingBreak`, and
  `appendBitVC_not_updateBinding` proves that it wins.
- The bridge-level append-bit example shows why the failure matters: a
  represented pre-state and an accepted committed write can coexist with a
  post-state commitment for which no represented full post-state exists.

## `Twostep.lean`

The goal of this file is to integrate memory reconstruction into a minimal
two-layer zkVM. Knowledge soundness of the final and segment argument systems
extracts and flattens a valid committed-state trace, proving `cte`. The memory
results then reconstruct a valid full-memory trace, proving `cte_full`. This is
the full-memory CTE theorem for the two-layer toy system, not yet the complete
Vanilla VM with its ISA, bus, and recursive proof layers.

- `SegStmt` and `SegWitness` describe a segment's committed boundaries,
  intermediate states, and explicit `MemStep` witnesses.
- `FinalStmt` and `FinalWitness` describe the whole committed execution through
  chained segment boundaries and proofs.
- `FinalStmtFull` carries the corresponding full-memory boundaries, and
  `toCommitted` commits such a boundary state.
- `System` packages the commitment scheme, memory-free step component, and
  verifier interfaces for the two-layer toy system.
- `RSeg` requires the segment boundaries to match and every explicit
  `MemStep` witness to satisfy `CommittedMemory.step`.
- `RFinal` requires the outer boundaries to match and every chained segment
  proof to verify.
- `toZkVM` and `toZkVMFull` instantiate the frozen abstract `ZkVM` with,
  respectively, committed and full-memory state semantics.
- `memoryStepInterface` instantiates the frozen committed-step interface, and
  `memoryBridge` proves its constructive bridge using `step_reconstruct`.
- `traceValid_full` turns a valid committed trace into a valid reconstructed
  full-memory trace with the correct endpoints.
- `cte` proves correct-trace extractability for the committed-state toy zkVM.
- `cte_full` proves correct-trace extractability for the full-memory toy zkVM.

## `TwostepSanity.lean`

The goal of this file is to show that all hypotheses of `cte_full` can hold
simultaneously in a concrete system. It constructs a one-segment, one-step
system over `exactVC`, uses relation witnesses as proofs with identity
extractors, exhibits an accepted final proof, and derives full-memory CTE. All
declarations are private, so the file adds no public API.

## Scope

Issue 1 establishes the committed-memory-to-full-memory bridge for the
two-layer toy system. It does not yet formalize the concrete ISA, the bus, or
the `convert`/`combine`/`embed` recursion tower. Those are separate issues in
[`PLAN.md`](PLAN.md), and this result must not be presented as the complete
Vanilla VM security theorem.
