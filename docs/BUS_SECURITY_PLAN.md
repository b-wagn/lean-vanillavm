# Bus Security: Audit and Repair Plan

> **Document status on `yl-memory-reconstruction`: alternative branch design.**
> This records the `canonicalStep`/`BusRefinesStep` approach explored on
> `yl-bus-modifications-draft`. Those identifiers are intentionally absent
> from the current branch, which instead connects `stepBus` definitionally to
> its memory descriptor and program semantics.

## What the pre-repair theorem really proved

The original `Bus.System.segment_extract` was logically meaningful. It did
**not** say that
an arbitrary `segmentVerify` function is knowledge-sound. Its hypothesis

```text
KnowledgeSound sys.ASSegment
```

assumes that this exact verifier is knowledge-sound for `RSegment`, whose
witness contains four accepted inner proofs. The theorem then composes that
extractor with the four inner extractors. Since all extracted buses hash to the
same public digest, perfect collision resistance identifies them, and the chip
predicates can be transported to the inner-step bus.

This is the proposition-level core of the whitepaper's segment-extraction and
bus-unification argument.

## Why that result was still under-specified

### 1. Its target is not the canonical VM step

The original file defined its semantic step as

```text
stepBus S1 S2 bus aux
  AND keccak bus
  AND poseidon bus
  AND range bus.
```

All four predicates are unconstrained fields of `Bus.System`. Consequently the
theorem establishes a trace for this internal conjunction, but no theorem says
that the conjunction implies `ZkVM.step`. The result stops before `Rstar`.

This is the main modeling gap identified in the meeting. It is not a flaw in
the Lean proof term; it is a missing semantic refinement theorem.

### 2. The collision reduction is hidden inside propositional rewriting

The proof applies injectivity directly to each pair of extracted buses. This
shows the right logical fact under a perfect assumption, but it does not expose
the algorithm that a computational proof would use to find a collision when
the buses differ.

### 3. The target argument system is hard to read

`ASSegment` and `ASSegmentTrace` reuse the same proof type and verifier while
being indexed by different relations. This is legitimate: the theorem
transports knowledge soundness from the proof-carrying relation to the semantic
relation. It is nevertheless easy to misread as a claim about an arbitrary
verifier because the relation is hidden behind the argument-system name.

The repaired public theorem should conclude `CTE` (or knowledge soundness of
`toCommittedZkVM.ASstar`) directly, so both the verifier and target relation are
visible through the central framework.

### 4. Operations are not classified

`stepBus` does not yet arise from concrete VanillaVM operation semantics. A
future instantiation must distinguish inline operations and delegated
operations and prove that every accepted bus step corresponds to one canonical
operation.

### 5. The result is committed-state security only

Even after the Bus repair, the segment trace contains committed-memory states.
It is an intermediate CTE theorem. Memory reconstruction must later lift it to
the full-memory `Rstar` intended by the paper.

## Threat model for this layer

Given an accepting segment proof, extraction may fail to produce a canonical
segment only if at least one of the following occurs:

1. the segment proof does not extract to four accepted inner proofs;
2. an accepted inner proof does not extract to a valid witness;
3. two inner witnesses use distinct buses with the same public digest;
4. all inner predicates hold on one bus, but their conjunction does not imply
   the canonical VM step.

Cases 1 and 2 are assigned to the corresponding knowledge-soundness
assumptions. Case 3 must produce an explicit bus-hash collision. Case 4 is not a
cryptographic failure: it is a semantic specification failure and must be
excluded by a separately proved `BusRefinesStep` theorem.

## Exact assumption ledger

| Premise or field | Category | What it supplies | What it does not supply |
|---|---|---|---|
| `hsegment` | cryptographic | Extracts four accepted inner proofs from an accepting `segmentVerify` proof | Correctness of any inner proof |
| `hstep` | cryptographic | Extracts committed states, step auxiliaries, and the step bus | Chip validity or full memory |
| `hkeccak`, `hposeidon`, `hrange` | cryptographic | Extract a bus satisfying the respective delegated predicate | Equality with the step bus |
| `hbus` | cryptographic, idealized | Excludes an explicit pair of distinct buses with one digest | An efficient or probabilistic hash theorem |
| `hrefine : BusRefinesStep` | semantic | Converts a bus-checked transition into `canonicalStep` | That the abstract predicates model the real VanillaVM ISA |
| `busEq` | structural/algorithmic | Implements the three bus comparisons | A running-time bound |
| `NsegPos` | structural | Rules out empty VanillaVM segments | Any total-step/divisibility fact used by recursion |

`segment_valid_or_collision` uses the semantic premise and the five extractor
correctness properties, but not `hbus`. `segment_extract` obtains those
extractors from the five knowledge-soundness premises and then uses `hbus` only
to rule out the explicit collision branch.

## Target model

`Bus.System` should contain two distinct predicates:

```lean
canonicalStep : CommittedVMState VC -> CommittedVMState VC -> Prop

stepBus : CommittedVMState VC -> CommittedVMState VC ->
  H.Domain -> StepAux -> Prop
```

and the following named obligation should be stated separately:

```lean
def BusRefinesStep (sys : System) : Prop :=
  forall S1 S2 bus aux,
    sys.stepBus S1 S2 bus aux ->
    sys.keccak bus ->
    sys.poseidon bus ->
    sys.range bus ->
    sys.canonicalStep S1 S2
```

The system can then instantiate the abstract framework:

```lean
def toCommittedZkVM (sys : System) : ZkVM where
  State := CommittedVMState sys.VC
  step := sys.canonicalStep
  T := sys.Nseg
  Stmt := SegmentStmt sys.VC
  initial := SegmentStmt.Sin
  terminal := SegmentStmt.Sout
  Proof := sys.SegmentProof
  verify := sys.segmentVerify
```

This makes the security target `sys.toCommittedZkVM.CTE`, rather than a local
relation whose connection to `Rstar` is implicit.

## Target theorem split

### Constructive theorem

The first theorem should make no collision-resistance assumption. In the
implemented interface, its statement receives the five concrete extractors and
their correctness proofs and names their exact composition:

```text
segment_valid_or_collision:
  correct inner and segment extractors
  + BusRefinesStep
  -> the named segmentReduction maps every accepting proof to
       either a valid canonical segment trace
       or a pair of distinct buses with the same digest.
```

The reduction must be a named definition. It should:

1. run the segment extractor once;
2. run each inner extractor once on the corresponding extracted proof;
3. compare the inner-step bus with the Keccak, Poseidon, and range buses;
4. return the first unequal pair, or return the extracted state trace if all
   buses agree.

Reusing the segment extraction result is important: a later cost theorem should
not accidentally charge or execute the adversary/outer extractor once per chip.

### Perfect-security corollary

The second theorem assumes `CollisionResistant sys.H`. It rules out the
collision branch and concludes:

```text
sys.toCommittedZkVM.CTE
```

This is still an idealized theorem, but its proof structure matches a genuine
computational reduction.

## Concrete operation integration

The abstract `BusRefinesStep` assumption must eventually be discharged for the
VanillaVM instance, rather than permanently postulated. The classified witness
should distinguish at least:

- read;
- write;
- ordinary inline operation;
- range-checked operation;
- Keccak call;
- Poseidon call;
- padding/no-op.

For each constructor, prove that:

- the claimed instruction is exactly the instruction fetched from the program
  at the pre-state program counter;
- the opcode/program-counter selection is correct;
- inline constraints imply the corresponding canonical operation predicate;
- every delegated call contributes its exact tagged bus entry;
- the matching chip predicate validates every entry with that tag;
- memory operations carry the explicit openings needed by memory extraction.

The concrete bus must preserve multiplicity (list/multiset or explicit indices),
and the protocol must choose whether extra validated entries are allowed. See
`CONCRETE_SEMANTICS_PLAN.md`. An opaque `H.Domain` with arbitrary predicates is
not an acceptable final instance.

The existential projection of this classified relation should be the binary
`canonicalStep` consumed by `ZkVM.Rstar`.

## Implementation stages

### Stage B0: explain and rename

- Document why `hsegment` prevents an arbitrary always-accepting verifier from
  making the theorem false.
- Rename the internal conjunction to `busCheckedStep`.
- Remove or de-emphasize `ASSegmentTrace` as the public target.

### Stage B1: connect to the abstract security goal

- Add `canonicalStep` to `Bus.System`.
- Define `BusRefinesStep`.
- Define `toCommittedZkVM`.
- Prove the CTE target using the current perfect collision-resistance
  assumption.

### Stage B2: expose the reduction

- Define a collision-candidate/result type.
- Define the named straight-line segment reduction.
- Prove `segment_valid_or_collision` without collision resistance.
- Derive the Stage B1 theorem as a corollary.

### Stage B3: make costs auditable

- Record exact extractor calls and shared intermediates.
- If a cost interface is used, prove exact composition equations.
- State clearly that the cost annotations require a manual or future
  machine-model justification.

### Stage B4: instantiate concrete operation semantics

- Integrate the memory step descriptor.
- Define the public/fixed program and instruction fetch.
- Replace the opaque concrete bus with tagged, multiplicity-preserving entries.
- Add delegated precompile/range constructors.
- Prove no-missing-entry and universal chip-coverage properties.
- Derive the concrete canonical step from instruction semantics.
- Prove `BusRefinesStep` by exhaustive instruction cases rather than assuming
  it.

### Stage B5: lift to full-memory CTE

- Use a pre-invariant-only `reconstructStep` theorem to construct memory across
  the segment; do not assume `CommitInv` for post-states.
- Consume completeness, position binding, and update binding through explicit
  valid-or-binding-break outputs.
- Prove the committed-to-full step bridge and commitment invariant at every
  index, then prove the claimed final full-memory boundary.
- Make the final target a full-memory `ZkVM` instance.

The off-image commitment counterexample and exact required interface are
audited in `MEMORY_INVARIANT_REVIEW.md`.

## Required negative tests and countermodels

Prefer formal countermodels showing that weakened global statements are false;
use compile-failure tests only when a type-level invariant is intended. The
review should reject or fail when:

- `hsegment` is removed;
- one inner knowledge-soundness assumption is removed;
- two different buses can share a digest without producing a collision branch;
- `BusRefinesStep` is removed while the theorem still claims canonical CTE;
- `canonicalStep` is replaced by `True` without this being visible in the
  concrete system instance;
- one chip predicate is omitted from the unified step;
- the reduction runs the segment extractor multiple times unintentionally;
- a theorem claims full-memory CTE while only committed states are extracted.

`Sanity.lean` currently covers arbitrary always-accept verification,
non-injective hashing, and a non-binding vector commitment. Concrete Bus tests
for missing entries, omitted chips, `canonicalStep := True`, and wrong-program
fetch remain part of Stage B4.

## Definition of done for Bus security

The Bus layer is complete when an accepting segment proof yields a canonical
committed segment or an explicit cryptographic break; the reduction is a named
inspectable function; collision resistance rules out the break; and the result
is stated as CTE/`Rstar` for the committed-state segment instance. Concrete
operation and memory layers must then discharge the remaining semantic bridge
to the final full-memory VanillaVM.

## Status on `yl-bus-modifications-draft`

Stages B0-B2 are implemented:

- `canonicalStep`, `BusRefinesStep`, and `toCommittedZkVM` expose the semantic
  target;
- `HashCollisionCandidate` and `IsHashCollision` expose the bad event;
- `busEq`, `unifyBuses`, and `segmentReduction` make the comparison algorithm
  inspectable;
- `segment_valid_or_collision` proves correctness of that exact algorithm
  without collision resistance;
- `segment_extract` obtains the component extractors from knowledge soundness,
  excludes the collision branch, and concludes committed-segment CTE.
- `NsegPos` rules out zero-instruction Bus instances.

Stages B3-B5 remain open. In particular, `BusRefinesStep` is still an abstract
premise; no concrete ISA instance, full-memory reconstruction, probability, or
running-time theorem is claimed. Therefore this status is a checked reduction
skeleton, not Bus security for VanillaVM.
