# Concrete Program, ISA, and Bus Plan

> **Document status on `yl-memory-reconstruction`: forward-looking proposal.**
> Its goals remain relevant, but some names describe the alternative
> `canonicalStep`/`BusRefinesStep` interface and have not yet been reconciled
> with this branch's `code`/`opcode`/`operation`/`memStep` interface.

## Objective

Replace the final use of arbitrary `canonicalStep`, `stepBus`, and chip
predicates with one auditable thin-slice VanillaVM instance. The first instance
is intentionally small enough for human review but contains every difficult
kind of interaction:

- `noop` and `add`: ordinary inline operations;
- `read` and `write`: committed/full-memory interaction;
- `keccak` and `poseidon`: fully delegated operations;
- `rangeAdd`: inline arithmetic plus a delegated range check.

Adding twenty arithmetic opcodes before these interfaces are sound would create
volume without resolving the architectural risks.

## Non-negotiable design rule

The final step relation is a **definition derived from a program and instruction
semantics**. It is not a field that an instance author may set to `True`.

The generic Bus theorem may remain parametric, but the public VanillaVM theorem
must consume only the concrete instance and proved bridge lemmas.

## Layer 1: program and instruction selection

The minimum program model should have the shape:

```lean
inductive Instr
  | noop
  | add      (dst src₁ src₂ : RegIndex)
  | read     (dst addrReg : RegIndex)
  | write    (addrReg valueReg : RegIndex)
  | rangeAdd (dst src₁ src₂ : RegIndex)
  | keccak   (args : KeccakArgs)
  | poseidon (args : PoseidonArgs)

structure Program where
  code : Word → Option Instr
```

`Option` makes an unmapped program counter explicitly invalid. Halting, if
needed, should be a dedicated instruction rather than an accidental missing
instruction.

Every operation relation must include:

```text
P.code S₁.pc = some instr
```

and its instruction-specific program-counter update. The canonical full step is
then:

```lean
def FullStep (P : Program) (S₁ S₂ : FullVMState VC) : Prop :=
  ∃ instr, P.code S₁.pc = some instr ∧ FullInstrStep P instr S₁ S₂
```

This prevents the wrong-program attack and makes opcode exhaustiveness visible
as case analysis on `Instr`.

### Word/address/value bridge

The current generic commitment uses `VC.Index` and `VC.Value`, whereas registers
hold `Word`. The concrete instance must choose and document one of:

1. `VC.Index = Addr` and `VC.Value = Byte/Word` by construction; or
2. explicit, checked conversion functions from register words to indices and
   values.

No hidden casts or unconstrained address/value witness fields are permitted.
For reads and writes, the descriptor fields must be proved equal to the values
decoded from the named registers.

## Layer 2: full and committed instruction semantics

Define two related instruction predicates:

- `FullInstrStep`: operates on explicit memory;
- `CommittedInstrStep`: operates on memory commitments and carries an explicit
  memory descriptor/opening.

The committed step witness should retain both instruction selection and all
security-relevant auxiliary data:

```lean
structure CommittedStepWitness where
  instr : Instr
  fetch : P.code pre.pc = some instr
  mem   : MemStep VC
  busRef : BusReference
```

The exact dependent encoding may differ, but it must be impossible for a read
or write proof to omit its opening. The existing `memory-integration` branch's
`MemStep`, `stepC`, `stepF`, `CommitInv`, `commitInv_write`, and
`step_mem_extract` are the starting point, not a parallel replacement. The
required stronger reconstruction interface and the reason update binding is
necessary are recorded in `MEMORY_INVARIANT_REVIEW.md`.

Required per-instruction reviews:

- exact registers read and written;
- word overflow/modulus semantics;
- program-counter update;
- memory preservation for non-write operations;
- address/value conversion;
- whether a bus entry is mandatory and what it contains.

## Layer 3: structured bus

The bus cannot remain an opaque `H.Domain`. Define a tagged entry type:

```lean
inductive BusEntry (VC : VectorCommitment)
  | keccak   (pre post : CommittedVMState VC) (args : KeccakArgs)
  | poseidon (pre post : CommittedVMState VC) (args : PoseidonArgs)
  | range    (state : CommittedVMState VC) (value : Word)

structure Bus (VC : VectorCommitment) where
  entries : List (BusEntry VC)
```

A list preserves multiplicity. If order is intentionally irrelevant, later
quotient by permutation or use a multiset and prove that the commitment matches
that representation. Do not silently use set membership when repeated calls
matter.

For the concrete Bus system, instantiate the hash commitment with
`H.Domain := Bus VC`. The actual encoding/serialization used before hashing is
a separate explicit function and must eventually match the circuit.

## Layer 4: coverage and chip predicates

Define chip validity by universal validation of tagged entries:

```text
KeccakValid B :=
  for every entry e in B.entries,
    if e is tagged keccak, then the concrete Keccak predicate holds
```

and analogously for Poseidon and range checks. The proof must not rely on a
vacuously true chip predicate unless the bus contains no entry with that tag.

`CommittedStepBus` case-splits on the fetched instruction:

- inline instructions prove their committed predicate directly;
- `rangeAdd` proves arithmetic inline and requires the exact range entry in the
  bus;
- Keccak/Poseidon require the exact precompile entry in the bus;
- read/write carry the explicit memory opening and do not delegate memory
  correctness to a chip.

This gives **no missing entries** by construction: a deferred instruction
cannot satisfy `CommittedStepBus` without its entry.

The extra-entry policy must be selected explicitly:

- **allowed and validated:** matches the whitepaper's formally stronger
  expanded predicate;
- **forbidden:** additionally prove every entry is referenced by a segment
  step;
- **optimized subset checking:** precisely state the subset and prove that it
  is sufficient.

The first option is the simplest sound thin-slice model.

## Layer 5: required bridge theorems

### Fetch and operation adequacy

```text
CommittedStepBus P Ŝ₁ Ŝ₂ B w
  -> w.fetch selects exactly P.code[Ŝ₁.pc]
```

### Bus elimination on committed states

```text
CommittedStepBus P Ŝ₁ Ŝ₂ B w
  + KeccakValid B + PoseidonValid B + RangeValid B
  -> CommittedStep P Ŝ₁ Ŝ₂ w
```

This is the concrete theorem that discharges the generic
`BusRefinesStep`. It must be proved by cases on the fetched `Instr`.

### One-step memory lift

```text
CommitInv Ŝ₁ S₁
  + CommittedStep P Ŝ₁ Ŝ₂ w
  + commitment completeness/binding
  -> exists S₂,
       CommitInv Ŝ₂ S₂
       AND FullStep P S₁ S₂
```

This extends/reuses `commitInv_write`, but unlike `step_mem_extract` it must not
assume `CommitInv` for the post-state. It explicitly constructs the post memory:
preserve it for reads/other operations and point-update it for writes.
`step_mem_extract` remains a secondary theorem for two already-related
endpoints. Memory reconstruction is separate from bus elimination so neither
theorem hides the other's assumptions.

### Segment reconstruction

```text
committed segment + initial full memory + per-step descriptors
  -> full segment preserving CommitInv at every index
  OR explicit binding-break witness
```

The reconstruction must define `memₖ₊₁` from `memₖ` and the instruction:
update for writes, preserve otherwise. Merely assuming full memories at both
endpoints satisfy `CommitInv` is not yet an extractor for a whole trace.

## Thin-slice completion gates

The concrete-semantics milestone is complete only when all of these hold:

1. `canonicalStep` for the concrete system is definitionally `FullStep P` or a
   named committed projection of it—not an arbitrary field.
2. Every `Instr` constructor has reviewed fetch, PC, register, memory, and bus
   behavior.
3. Read/write descriptors are tied to the concrete registers.
4. The bus is tagged and multiplicity-preserving.
5. Deferred steps require their exact entries.
6. Chip predicates validate every tagged entry under the chosen extra-entry
   policy.
7. The concrete `BusRefinesStep` theorem is proved by exhaustive cases.
8. One-step memory lifting consumes completeness, position binding, and
   update binding, and does not assume the post commitment invariant.
9. A trace-level reconstruction maintains `CommitInv` inductively.
10. At least one negative concrete instance demonstrates that omitting a bus
    entry or program fetch makes the step relation false.

Only after this thin slice passes human review should the remaining RV32IM and
precompile operations be added.
