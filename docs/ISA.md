# Human review guide — representative ISA (Issue 3)

> **Review-version warning.** This guide and the Lean files it describes form
> one versioned review unit: it applies only when read at the same Git commit as
> the code. Any later change to the declarations below must update this guide
> and reopen the affected `CORRESPONDENCE.md` rows. A GitHub approval should
> therefore target the PR's current head commit, not an earlier revision.

## File-level overview

### `Memory.lean`

The Issue 3 change generalizes `FullMemory.read` and `FullMemory.write` so they
work with any memory index and value types. Their logical meaning is unchanged;
this allows the new ISA to reuse the existing memory equations with ordinary
`Addr → Byte` memory instead of duplicating them. The file also documents that
reads leave memory unchanged, as required by the paper’s read semantics.

- `FullMemory.read`: describes a correct read between full-memory states:
  - the PC/register requirements hold;
  - the value at the selected address equals the loaded value;
  - the output memory is identical to the input memory.

- `FullMemory.write`: describes a correct write:
  - the PC/register requirements hold;
  - the selected address contains the new value in the output state;
  - every other memory address is unchanged.

- Both definitions are parameterized by their memory index and value types.
  This lets the commitment reconstruction layer and the ordinary `Addr → Byte`
  ISA use exactly the same equations.

- This is a type-level generalization only; the logical conditions imposed by
  the definitions are unchanged.

- `step_reconstruct_exact`: reconstructs the next full-memory state while
  retaining the same explicit `MemStep` in the conclusion. The ISA theorem uses
  that same value to carry the program/register checks from the committed
  transition to the reconstructed plain transition.

### `ISA.lean`

The goal of this file is to define the representative plain-state instruction
semantics required by Issue 3. It divides instructions into five classes
(`read`, `write`, `arith`, `hash`, and `bin`) and defines a single-step
predicate as the disjunction of those five cases. Exact RV32IM instruction
semantics remain abstract, but instruction selection and all memory behavior
are explicit.

The file does not verify an opcode decoder, concrete arithmetic implementation,
hash chip, or bus consistency. It does connect the selected operation to the
`MemStep` used by committed-memory reconstruction. `VMs/Bus.lean` now adds the
bus and chip checks as a separate layer without changing this ISA definition.

- `OperationClass`: the five representative classes:
  - `read`: loads a value from memory;
  - `write`: changes one memory location;
  - `arith`: represents arithmetic instructions;
  - `hash`: represents Keccak and Poseidon calls;
  - `bin`: represents binary and bitwise instructions.

- `OperationClass` describes categories, not exact decoded instructions. This
  distinction is made explicit so that the formalization is not mistaken for
  an opcode-level RV32IM verification.

- `System`: packages the data needed to define the ISA:
  - `code : Word → OperationClass` records the class of the instruction at each
    program counter;
  - `memFreePred : OperationClass → MemFreePredicate` supplies the remaining
    PC/register requirements for each class;
  - `indexOfWord : Word → Index` interprets the address register in the
    memory's index type;
  - `valueOfWord : Word → Value` interprets a register in the memory's value
    type.

- The ordinary paper state still uses `Addr → Byte` memory. These names remain
  useful: `Addr` and `Byte` identify the roles played by the otherwise abstract
  natural numbers, and `VMState` names exactly the state described in Chapter
  1. `VMStateWith` is the only Lean structure containing the `pc`, `regs`, and
  `mem` fields. `FullVMState VC` uses that same structure with the address and
  value types chosen by `VC`; it does not define another state with different
  fields or behavior.

- Although `code` records only an operation class, `memFreePred` receives the
  program counter and can therefore impose instruction-specific behavior at
  each program location.

- For reads and writes, `memFreePred` is also responsible for any required
  address-bound checks because those checks depend only on registers.

- `System.operation`: defines the complete predicate `φ_op` for one selected
  operation class. Every case first requires `code S₁.pc = op`, ensuring that
  the operation agrees with the fixed program.

- In the `read` case:
  - `indexOfWord` interprets register 0 of the input state as the address;
  - `valueOfWord` interprets register 1 of the output state as the loaded value;
  - `FullMemory.read` checks that the value is present and that memory is
    unchanged.

- In the `write` case:
  - `indexOfWord` interprets register 0 of the input state as the address;
  - `valueOfWord` interprets register 1 of the input state as the new value;
  - `FullMemory.write` checks that exactly that address is updated.

- In the `arith`, `hash`, and `bin` cases:
  - the corresponding PC/register predicate must hold;
  - the output memory must equal the input memory.

- `System.stepPlain`: the plain-state step predicate `φ_step`. A step is valid
  exactly when one of the five `System.operation` cases holds.

- `System.stepPlain_iff_operation_at_pc`: shows that the five-way disjunction
  is equivalent to executing the single operation class stored at
  `code S₁.pc`. A proof therefore cannot choose a different class merely by
  selecting a different disjunct.

- `System.operation_preserves_memory_unless_write`: proves that every accepted
  operation other than `write` leaves memory unchanged. In particular, this
  prevents a read, arithmetic operation, hash call, or binary operation from
  silently replacing memory.

- `System.selectedMemFreePred`: selects the PC/register predicate belonging to
  `code[pc]`. This is a helper shared by the committed and full-memory
  equations, not another step relation.

- `System.committedOperation`: checks one explicit `MemStep` against the
  committed-memory equations and the fixed program. A read/write witness must
  have the constructor selected by `code[pc]`, and its address/value must equal
  the values obtained from the designated registers. `.other` is permitted
  only for `arith`, `hash`, or `bin`.

- `System.committedStep`: says that some `MemStep` passes
  `committedOperation`. A caller checking only whether two committed states are
  connected does not provide that value explicitly. Segment witnesses still
  store it because memory reconstruction needs its opening proof.

- `System.committedOperation_stepPlain`: if memory reconstruction realizes the
  same accepted `MemStep` between represented full states, then those states
  satisfy `stepPlain`.

- `stepPlain` is now `TwoStep.System.toZkVM.step`; it is not an independent
  security definition or an additional execution relation.

### `TwoStep/TwoStep.lean`

The goal of the Issue 3 changes in this file is to make the representative ISA
the actual execution semantics of the existing two-layer VM. Segment witnesses
still contain memory openings, but they must agree with the fixed program; the
memory-reconstruction proof then establishes `stepPlain` for every reconstructed
transition.

- `System.isa`: replaces the single undifferentiated memory-free predicate with
  the fixed program and its five class-specific predicates.

- `RSeg`: requires every explicit `MemStep` to satisfy
  `ISA.System.committedOperation`, including the `code[pc]` and register-field
  checks.

- `CommittedTraceValid`: uses `ISA.System.committedStep`, which records that
  some explicit `MemStep` passes the same checks at each transition.

- `toZkVM`: sets its `step` field directly to `ISA.System.stepPlain`. The
  theorem `stepPlain_iff_operation_at_pc` shows that this is exactly the
  `operation` chosen by `code[pc]`. There is no arbitrary `MemStep` in the
  plain execution predicate.

- `memoryBridge`: reconstructs the next represented state for the same
  accepted `MemStep`, then proves that the full-state transition satisfies
  `stepPlain`.

- `traceValid_full`: performs the same argument over the complete committed
  trace, preserving both the commitment invariant and agreement with the fixed
  program at each index.

- `cte`: consequently proves correct-trace extractability for the two-layer VM
  using `stepPlain`, rather than for a weaker memory-only execution relation.

### `ISASanity.lean`

The goal of this file is to demonstrate that the ISA definitions admit
expected executions and reject malformed ones. It provides accepted read and
changed-memory write examples, rejects a step with the wrong operation class,
and rejects a write whose output memory is incorrect. It also constructs a
private `ZkVM` using `stepPlain` directly as its `step` field, confirming that
Issue 3 has not introduced a second, unrelated top-level execution relation.

All declarations are private, so this file checks the definitions without
expanding the public API.

- `systemFor`: constructs a small private system whose program always contains
  one selected operation class and whose PC/register predicate always accepts.
  It isolates the memory and instruction-selection equations for testing.

- `zeroState`: a state with zero program counter, registers, and memory.

- `accepts_read`: demonstrates an actual state transition satisfying the read
  case.

- `beforeWrite` and `afterWrite`: define states whose memories differ at the
  address selected by the write registers.

- `accepts_changed_write`: demonstrates that a correctly updated memory
  satisfies `stepPlain`.

- `rejects_wrong_fetch`: demonstrates that a system whose program selects
  `write` cannot satisfy the `read` predicate at the same program counter.

- `rejects_incorrect_write_result`: demonstrates that a write is rejected when
  the requested value is not placed in memory.

- `readZkVM`: a private abstract `ZkVM` whose `step` field is exactly
  `ISA.System.stepPlain`.

- `concrete_zkVM_uses_stepPlain`: confirms that the private VM’s `step`
  relation accepts the read example.

- Together, these examples show that the definitions are usable, that their
  important checks are not vacuous, and that accepted steps are tied to the
  selected program class.

### `TwoStep/TwoStepSanity.lean`

The existing private one-step model now instantiates an arithmetic program,
uses an accepted `.other` `MemStep`, rejects a read `MemStep` at that same
program counter, and checks both an actual `toZkVM.step` and the complete `cte`
theorem. This shows that the ISA-aware segment assumptions, memory assumptions,
and knowledge-soundness assumptions remain jointly satisfiable.

## Human review checklist

The reviewer should check the following definitions and theorem statements
against the cited paper sections, without relying only on the fact that the
proofs compile:

1. `OperationClass` is an explicitly representative five-class simplification,
   and no comment claims complete RV32IM coverage.
2. Every `operation` includes `code S₁.pc = op`; reads preserve memory, writes
   change only the selected address, and the other three classes preserve
   memory.
3. `committedOperation` rejects a `MemStep` constructor inconsistent with
   `code[pc]` and ties read/write address and value fields to the designated
   registers.
4. `TwoStep.System.toZkVM.step` is assigned `stepPlain`, which is proved equal
   to the `operation` selected by `code[pc]`. Both the one-step and trace
   reconstruction arguments keep the same `MemStep` long enough to prove this
   fact.
5. The new address/value interpretation functions only convert register words
   to the address and value types used by a commitment; they do not introduce
   a second kind of state or a second execution rule.
6. The sanity models demonstrate accepted read/write/non-memory behavior and
   reject wrong fetches and incorrect write results.

After completing that review, the reviewer should update the Issue 3
`Fidelity`, `Complete`, and `Reviewer` cells in `CORRESPONDENCE.md` in a
separate review commit. This keeps implementation changes distinct from human
sign-off and records exactly which commit was reviewed.

## Scope of the result

Issue 3 establishes the representative plain-execution predicate and connects
it to the committed `MemStep` data used by the two-layer VM. This file does not
itself add bus evidence, prove individual RV32IM opcodes, or construct the
complete recursive Vanilla VM. Issue 5's `VMs/Bus.lean` adds the separate bus
and chip checks, while Issue 7 assembles the final VM.
