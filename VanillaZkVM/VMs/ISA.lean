import VanillaZkVM.VMs.Memory

/-!
# Representative Vanilla VM operation classes

This module supplies the plain-state step predicate that later Vanilla VM
instances use as `ZkVM.step`. It deliberately models five operation classes
rather than the whitepaper's complete opcode list:
`read`, `write`, `arith`, `hash`, and `bin`.

## Main definitions
* `OperationClass` — the five representative operation classes.
* `System` — the class of the instruction at each program counter and the
  opaque PC/register predicate `φ'_op` for each class.
* `System.operation` — `φ_op`, including the class check and the operation's
  explicit memory equation.
* `System.stepPlain` — `φ_step`, the disjunction of the five operation
  classes.

## Main result
* `System.stepPlain_iff_operation_at_pc` — a valid step is exactly the
  operation selected by the program at the current program counter.
* `System.operation_preserves_memory_unless_write` — every operation class other
  than `write` leaves memory unchanged.

The PC/register semantics remain black-box predicates, as they do in the
paper. They may still distinguish the exact instruction at a program counter;
only the five-way case split is abstracted. Memory behavior is explicit: reads
use register 0 as the address and register 1 of the second state as the loaded
value; writes use registers 0 and 1 of the first state as the address and value;
all other classes preserve memory.

Paper: `eq:phiop`, `eq:phi-read-decomp`, and `eq:phi-write-decomp` (ch01), and
the operation taxonomy and `eq:step` (ch03), deliberately simplified to the
five classes specified by Issue 3.
-/

namespace VanillaZkVM
namespace ISA

/-! ## Operation classes and fixed ISA parameters -/

/-- The five operation classes modeled by this formalization.

`hash` represents the hash-call precompiles (Keccak and Poseidon), `arith`
represents arithmetic operations, and `bin` represents binary/bitwise
operations. The separate bus layer can use the `hash` class to identify calls
that must be checked by a hash chip. A value of this type identifies a class,
not an exact decoded instruction. This is the intentional simplification
required by Issue 3, not a complete RV32IM opcode enumeration.

Paper: operation taxonomy in ch03, with the deliberate five-operation
simplification documented in `docs/CORRESPONDENCE.md`. -/
inductive OperationClass where
  | read
  | write
  | arith
  | hash
  | bin
  deriving DecidableEq, Repr

/-- The parameters needed to interpret the five operation classes.

`code` is the class-level view of the fixed program: it records which of the
five cases applies at each program counter. `memFreePred` contains the exact
PC/register requirements for that class and may use the program counter to
distinguish instructions within it. The definition `operation` combines these
requirements with the class check and the appropriate memory equation. For a
read or write, `memFreePred` must also enforce any required address bounds,
because those bounds depend only on registers.

Paper: `eq:phiop` and the `φ'_op` decomposition in ch01/ch03. -/
structure System where
  /-- The operation class of the instruction at each program counter. -/
  code : Word → OperationClass
  /-- The PC/register requirements `φ'_op` for each operation class. -/
  memFreePred : OperationClass → MemFreePredicate

namespace System

variable (isa : System)

/-! ## Full operation predicates and the canonical plain step -/

/-- The full predicate `φ_op` for one operation class.

Every case checks that `code S₁.pc = op`. The read and write cases reuse
`FullMemory.read` and `FullMemory.write`, selecting their address/value
arguments from the registers prescribed by the paper. The remaining cases
combine their PC/register requirements with `S₂.mem = S₁.mem`.

The read case therefore includes `S₂.mem = S₁.mem`. The pinned decomposition
formula omits this explicit condition even though the paper says that reads do
not change memory; `FullMemory.read` and `docs/PAPER_REVISION.md` explain the
paper-side correction.

Paper: `eq:phiop`, `eq:phi-read-decomp`, `eq:phi-write-decomp` (ch01), and the
non-memory-operation equation immediately before `eq:step` (ch03). -/
def operation (op : OperationClass) (S₁ S₂ : VMState) : Prop :=
  isa.code S₁.pc = op ∧
    match op with
    | .read =>
        FullMemory.read (isa.memFreePred .read) (S₁.regs 0) (S₂.regs 1) S₁ S₂
    | .write =>
        FullMemory.write (isa.memFreePred .write) (S₁.regs 0) (S₁.regs 1) S₁ S₂
    | .arith =>
        isa.memFreePred .arith S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem
    | .hash =>
        isa.memFreePred .hash S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem
    | .bin =>
        isa.memFreePred .bin S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem

/-- The canonical plain-state step predicate `φ_step`. It holds when one of
the five operation-class predicates holds. Each clause checks that the class
matches the instruction at the current program counter.

Concrete Vanilla VM constructions must use this predicate as their
`ZkVM.step`; it is not an additional step relation beside `ZkVM.step`.

Paper: `eq:step` (ch03), with the deliberate five-operation simplification
documented in `docs/CORRESPONDENCE.md`. -/
def stepPlain (S₁ S₂ : VMState) : Prop :=
  isa.operation .read S₁ S₂ ∨
  isa.operation .write S₁ S₂ ∨
  isa.operation .arith S₁ S₂ ∨
  isa.operation .hash S₁ S₂ ∨
  isa.operation .bin S₁ S₂

/-- A plain step executes exactly the operation class stored in the program at
the current program counter. Thus the disjunction in `stepPlain` does not let a
proof choose an unrelated operation: the `code S₁.pc = op` conjunct in
`operation` fixes the only possible branch.

Paper: instruction selection in `eq:op` and `eq:phiop` (ch01), and the
disjunctive step predicate `eq:step` (ch03). -/
theorem stepPlain_iff_operation_at_pc (S₁ S₂ : VMState) :
    isa.stepPlain S₁ S₂ ↔ isa.operation (isa.code S₁.pc) S₁ S₂ := by
  cases hcode : isa.code S₁.pc <;> simp [stepPlain, operation, hcode]

/-- Every operation class except `write` preserves memory. In
particular, this covers `read`, `arith`, `hash`, and `bin`; the read predicate
also checks the loaded value at the selected address.

Paper: memory-operation semantics in ch01 and the non-memory-operation
equation immediately before `eq:step` (ch03). -/
theorem operation_preserves_memory_unless_write
    (op : OperationClass) (S₁ S₂ : VMState) (hop : op ≠ .write)
    (h : isa.operation op S₁ S₂) :
    S₂.mem = S₁.mem := by
  cases op <;> simp_all [operation, FullMemory.read]

end System
end ISA
end VanillaZkVM
