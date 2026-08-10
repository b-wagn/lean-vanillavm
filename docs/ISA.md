# Human review guide — representative ISA (Issue 3)

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

### `ISA.lean`

The goal of this file is to define the representative plain-state instruction
semantics required by Issue 3. It divides instructions into five classes
(`read`, `write`, `arith`, `hash`, and `bin`) and defines a single-step
predicate as the disjunction of those five cases. Exact RV32IM instruction
semantics remain abstract, but instruction selection and all memory behavior
are explicit.

The file does not yet verify an opcode decoder, concrete arithmetic
implementation, hash chip, committed-memory execution, or bus consistency.
Those belong to later issues.

- `OperationClass`: the five representative classes:
  - `read`: loads a value from memory;
  - `write`: changes one memory location;
  - `arith`: represents arithmetic instructions;
  - `hash`: represents Keccak and Poseidon calls;
  - `bin`: represents binary and bitwise instructions.

- `OperationClass` describes categories, not exact decoded instructions. This
  distinction is made explicit so that the formalization is not mistaken for
  an opcode-level RV32IM verification.

- `System`: packages the two pieces needed to define the ISA:
  - `code : Word → OperationClass` records the class of the instruction at each
    program counter;
  - `memFreePred : OperationClass → MemFreePredicate` supplies the remaining
    PC/register requirements for each class.

- Although `code` records only an operation class, `memFreePred` receives the
  program counter and can therefore impose instruction-specific behavior at
  each program location.

- For reads and writes, `memFreePred` is also responsible for any required
  address-bound checks because those checks depend only on registers.

- `System.operation`: defines the complete predicate `φ_op` for one selected
  operation class. Every case first requires `code S₁.pc = op`, ensuring that
  the operation agrees with the fixed program.

- In the `read` case:
  - register 0 of the input state supplies the address;
  - register 1 of the output state supplies the loaded value;
  - `FullMemory.read` checks that the value is present and that memory is
    unchanged.

- In the `write` case:
  - register 0 of the input state supplies the address;
  - register 1 of the input state supplies the new value;
  - `FullMemory.write` checks that exactly that address is updated.

- In the `arith`, `hash`, and `bin` cases:
  - the corresponding PC/register predicate must hold;
  - the output memory must equal the input memory.

- `System.stepPlain`: the plain-state step predicate `φ_step`. A step is valid
  exactly when one of the five `System.operation` cases holds.

- `System.operation_preserves_memory_unless_write`: proves that every accepted
  operation other than `write` leaves memory unchanged. In particular, this
  prevents a read, arithmetic operation, hash call, or binary operation from
  silently replacing memory.

- `stepPlain` is intended to become the eventual concrete Vanilla VM’s
  `ZkVM.step`; it is not an independent security definition or an additional
  execution relation.

### `ISASanity.lean`

The goal of this file is to demonstrate that the ISA definitions admit
expected executions and reject malformed ones. It provides accepted read and
changed-memory write examples, rejects a step with the wrong operation class,
and rejects a write whose output memory is incorrect. It also constructs a
private `ZkVM` using `stepPlain` directly as its `step` field, confirming that
Issue 3 has not introduced a competing top-level execution relation.

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

- `concrete_zkVM_uses_stepPlain`: confirms that the private VM’s canonical step
  relation accepts the read example.

- Together, these examples show that the definitions are usable, that their
  important checks are not vacuous, and that accepted steps are tied to the
  selected program class.

## Scope of the result

Issue 3 establishes the representative plain-execution predicate needed by the
eventual Vanilla VM. It does not yet connect an operation class to extracted
`MemStep` data or bus evidence, prove the correctness of individual RV32IM
opcodes, or construct the complete recursive zkVM. Issue 5 will add the
committed/bus-backed step layer, while Issue 7 will assemble the final public
`ZkVM` instance.
