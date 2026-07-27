# Memory Reconstruction Proof Contract

## Claim

This branch formalizes the qualitative committed-to-full-memory reconstruction
step that was missing from the VanillaVM security argument.

Given:

- an initial full state whose memory honestly commits to the extracted initial
  committed state;
- for the exact-boundary theorem, a claimed terminal full state whose memory
  honestly commits to the extracted terminal committed state;
- one explicit read/write/other descriptor per committed transition;
- completeness, position binding, and update binding of the memory commitment;
- a valid committed step at every index;

`reconstructTrace_correct` constructs a full-memory trace with exact initial
and final full-state boundaries and proves the full-memory step predicate at
every transition.

The memory result is standalone, and `BusMemory.lean` now composes it with the
Bus extractor for one segment. It is not yet connected to a concrete VanillaVM
ISA/program, the multi-segment final/recursive extractor, or a computational
probability bound.

## Why update binding is necessary

Position binding and the former punctured-binding condition constrain accepted
openings but do not force an accepted root to be an honest output of `commit`.
Appending a verifier-ignored bit gives a counterexample:

```text
Commit'(memory) = (Commit(memory), false)
Verify'((root, bit), ...) = Verify(root, ...)
```

Roots ending in `true` accept the same openings but cannot equal
`Commit'(memory)` for any memory. `MemorySanity.appendBitVC` formalizes this
construction. It satisfies completeness, position binding, and punctured
binding, while `appendBitVC_not_updateBinding` proves that update binding fails.

## Module and theorem map

### `Crypto.lean`

- `Complete`
- `UpdateBinding`
- `PositionBindingBreak` / `IsPositionBindingBreak`
- `UpdateBindingBreak` / `IsUpdateBindingBreak`
- theorems showing the binding properties rule out certified failures
- `mem_eq_of_commit_eq`

### `Memory.lean`

- committed/full states and `CommitInv`
- classified `MemStep`
- committed predicates `stepC` and full predicates `stepF`
- `reconstructStepReduction`: named deterministic reduction
- `reconstructStepReduction_correct`: success-or-certified-break proof
- `reconstructStepReduction_success`: binding rules out both failures
- `reconstructStep`: pre-invariant-only existential reconstruction
- `step_mem_extract`: secondary transfer theorem when both endpoint invariants
  are already supplied
- `commit_update` and `commitInv_write`

The security-critical difference is:

```text
step_mem_extract:
  CommitInv pre + CommitInv post + committed step -> full step

reconstructStep:
  CommitInv pre + committed step
    -> exists post, CommitInv post + full step
```

Only the latter can serve as the induction unit for trace reconstruction.

### `MemoryTrace.lean`

- `reconstructTrace`: deterministic iteration of the one-step reduction
- a potentially different core/program predicate at each trace index
- `reconstructTrace_commitInv`: invariant at every state
- `reconstructTrace_step`: full semantics at every transition
- `reconstructTrace_from_initial`: primary theorem; constructs all later
  invariants from only the initial one
- `reconstructTrace_terminal`: equality with the claimed full terminal state
- `reconstructTrace_correct`: exact-terminal corollary when the public terminal
  full state is also known to open the terminal commitment

### `MemorySanity.lean`

- `exactVC`: a non-succinct model satisfying all three required properties
- `exactVC_accepts_changed_write`: positive non-vacuity test with distinct
  pre/post roots and one shared authentication proof
- `appendBitVC`: the ignored-bit attack
- `appendBitBreak_wins`: an explicit update-binding failure record
- `appendBitVC_not_updateBinding`: old assumptions do not close the gap

### `Bus.lean` and `BusMemory.lean`

- `Bus.System.Nseg_pos`: zero-length segment configurations are excluded
- `Bus.System.memStep`: every extracted auxiliary witness retains its
  read/write/other descriptor
- `Bus.System.code` and `opcode`: an explicit fixed program and the instruction
  selected by each auxiliary witness
- `Bus.System.coreStep`: definitionally checks `code[pre.pc] = opcode(aux)`
  before the per-operation PC/register predicate
- `Bus.System.stepBus`: definitionally equal to `Memory.stepC`; there is no
  unconstrained `BusRefinesStep` hypothesis
- `segment_reconstruct_memory`: a semantic Bus segment witness reconstructs to
  a full-memory trace and maintains `CommitInv` at every index
- `accepting_segment_reconstructs_memory`: an accepting segment proof is first
  extracted and bus-unified, then reconstructed to a full-memory segment trace

The individual `operation` predicates remain abstract specification
parameters. Consequently, these theorems become statements about the actual
VanillaVM only after `code`, `opcode`, `operation`, and `memStep` are
instantiated from a concrete program/ISA.

## Explicit reduction behavior

For a read:

```text
known pre-memory value = descriptor value
  -> reconstruct unchanged post-memory
  -> otherwise return a position-binding break
```

For a write:

```text
known old value = descriptor old value
  -> candidate post-root = Commit(point update)
       -> reconstruct the point-updated post-memory
       -> otherwise return an update-binding break
  -> otherwise return a position-binding break
```

For another operation, memory and its commitment are preserved.

`reconstructStepReduction_correct` assumes only commitment completeness,
the pre-state invariant, and the committed step. Position and update binding
appear only in the security corollary that excludes the two explicit failure
branches.

## Axiom audit

Audit performed with the pinned Lean/Mathlib toolchain:

| Declaration | Reported axioms |
|---|---|
| `reconstructStepReduction_correct` | `propext` |
| `reconstructStepReduction_success` | `propext` |
| `reconstructStep` | `propext` |
| `commit_update` | none |
| `commitInv_write` | none |
| `step_mem_extract` | `propext`, `Classical.choice`, `Quot.sound` |
| `reconstructTrace_commitInv` | `propext` |
| `reconstructTrace_step` | `propext` |
| `reconstructTrace_from_initial` | `propext` |
| `reconstructTrace_terminal` | `propext`, `Quot.sound` |
| `reconstructTrace_correct` | `propext`, `Quot.sound` |
| `Bus.System.segment_extract` | none |
| `Bus.System.segment_reconstruct_memory` | `propext` |
| `Bus.System.accepting_segment_reconstructs_memory` | `propext` |
| `exactVC_updateBinding` | `Quot.sound` |
| `exactVC_accepts_changed_write` | `propext` |
| `appendBitBreak_wins` | none |
| `appendBitVC_not_updateBinding` | none |

There are no `sorry` or custom axioms. This audit establishes proof-term trust,
not semantic adequacy or computational cryptographic security.

## Remaining integration work

1. Instantiate `Bus.System.code`, `opcode`, `operation`, and `memStep` from one
   concrete program/ISA. Opcode fetch is now structural; the instruction
   predicates and register behavior still require a reviewed instance.
2. Replace the opaque bus domain/predicates with typed entries and prove
   referenced-entry membership and complete chip coverage.
3. Flatten `StepAux`/memory descriptors together with states across all
   segments, rather than only reconstructing one segment.
4. Compose that flattened result with the final and
   convert/combine/embed extractors, then target full-memory `Rstar`/CTE.
5. Replace the trace-level impossible-branch fallback with a finite
   success-or-indexed-binding-break result for the computational theorem.
6. Prove update binding for the chosen Merkle commitment via an explicit hash
   collision reduction.
7. Add probabilities, security parameters, and running-time accounting.

Until those steps are complete, the accurate claim is:

> Lean checks the qualitative Bus-to-full-memory segment reduction under
> perfect knowledge soundness, collision resistance, completeness, position
> binding, and update binding, relative to abstract operation predicates.
