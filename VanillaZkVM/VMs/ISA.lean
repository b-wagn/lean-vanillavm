import VanillaZkVM.VMs.Memory

/-!
# Representative Vanilla VM operation classes

This module supplies the plain-state step predicate that later Vanilla VM
instances use as `ZkVM.step`. It deliberately models five operation classes
rather than the whitepaper's complete opcode list:
`read`, `write`, `arith`, `hash`, and `bin`.

## Main definitions
* `OperationClass` — the five representative operation classes.
* `System` — the class of the instruction at each program counter, the
  PC/register requirements left abstract by this issue, and the functions that
  interpret register words as memory addresses and values.
* `System.operation` — `φ_op`, including the class check and the operation's
  explicit memory equation.
* `System.stepPlain` — `φ_step`, the disjunction of the five operation
  classes.
* `System.committedOperation` — checks a particular `MemStep` against the
  program and committed-memory equations.
* `System.committedStep` — says that some `MemStep` passes those checks.

## Main result
* `System.stepPlain_iff_operation_at_pc` — a valid step is exactly the
  operation selected by the program at the current program counter.
* `System.operation_preserves_memory_unless_write` — every operation class
  other than `write` leaves memory unchanged.
* `System.committedOperation_stepPlain` — after memory reconstruction, an
  accepted committed operation satisfies the single plain step predicate used
  as `ZkVM.step`.

The exact PC/register semantics remain abstract predicates, as they do in the
paper. They may still distinguish the exact instruction at a program counter;
only the five-way case split is simplified. Memory behavior is explicit: reads
interpret register 0 as the address and register 1 of the second state as the
loaded value; writes interpret registers 0 and 1 of the first state as the
address and value; all other classes preserve memory.

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
five cases applies at each program counter. `memFreePred` contains the remaining
PC/register requirements for that class and may use the program counter to
distinguish instructions within it. The definition `operation` combines these
requirements with the class check and the appropriate memory equation. For a
read or write, `memFreePred` must also enforce any required address bounds,
because those bounds depend only on registers.

`Index` and `Value` are parameters so this ISA works both with the paper's
ordinary `Addr → Byte` memory and with the address and value types chosen by a
commitment scheme. `indexOfWord` and `valueOfWord` state explicitly how a
machine word is interpreted as one of those addresses or values. For the
paper's current `ℕ`-based types, both functions are simply the identity.

Paper: `eq:phiop` and the `φ'_op` decomposition in ch01/ch03. -/
structure System (Index Value : Type) where
  /-- The operation class of the instruction at each program counter. -/
  code : Word → OperationClass
  /-- The PC/register requirements `φ'_op` for each operation class. -/
  memFreePred : OperationClass → MemFreePredicate
  /-- Interpret the address register as an index in this system's memory. -/
  indexOfWord : Word → Index
  /-- Interpret a register word as a value in this system's memory. -/
  valueOfWord : Word → Value

namespace System

variable {Index Value : Type} (isa : System Index Value)

/-! ## Full operation predicates and the single plain step -/

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
def operation (op : OperationClass) (S₁ S₂ : VMStateWith (Index → Value)) : Prop :=
  isa.code S₁.pc = op ∧
    match op with
    | .read =>
        FullMemory.read (isa.memFreePred .read)
          (isa.indexOfWord (S₁.regs 0)) (isa.valueOfWord (S₂.regs 1)) S₁ S₂
    | .write =>
        FullMemory.write (isa.memFreePred .write)
          (isa.indexOfWord (S₁.regs 0)) (isa.valueOfWord (S₁.regs 1)) S₁ S₂
    | .arith =>
        isa.memFreePred .arith S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem
    | .hash =>
        isa.memFreePred .hash S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem
    | .bin =>
        isa.memFreePred .bin S₁.pc S₁.regs S₂.pc S₂.regs ∧ S₂.mem = S₁.mem

/-- The plain-state step predicate `φ_step` used as `ZkVM.step`. It holds when
one of the five operation-class predicates holds. Each clause checks that the
class matches the instruction at the current program counter.

Concrete Vanilla VM constructions must use this predicate as their
`ZkVM.step`; it is not an additional step relation beside `ZkVM.step`.

Paper: `eq:step` (ch03), with the deliberate five-operation simplification
documented in `docs/CORRESPONDENCE.md`. -/
def stepPlain (S₁ S₂ : VMStateWith (Index → Value)) : Prop :=
  isa.operation .read S₁ S₂ ∨
  isa.operation .write S₁ S₂ ∨
  isa.operation .arith S₁ S₂ ∨
  isa.operation .hash S₁ S₂ ∨
  isa.operation .bin S₁ S₂

/-- A plain step executes exactly the operation class stored in the program at
the current program counter. Thus the disjunction in `stepPlain` does not let a
proof choose an unrelated operation: the condition `code S₁.pc = op` in
`operation` fixes the only possible branch.

Paper: instruction selection in `eq:op` and `eq:phiop` (ch01), and the
disjunctive step predicate `eq:step` (ch03). -/
theorem stepPlain_iff_operation_at_pc (S₁ S₂ : VMStateWith (Index → Value)) :
    isa.stepPlain S₁ S₂ ↔ isa.operation (isa.code S₁.pc) S₁ S₂ := by
  cases hcode : isa.code S₁.pc <;> simp [stepPlain, operation, hcode]

/-- Every operation class except `write` preserves memory. In
particular, this covers `read`, `arith`, `hash`, and `bin`; the read predicate
also checks the loaded value at the selected address.

Paper: memory-operation semantics in ch01 and the non-memory-operation
equation immediately before `eq:step` (ch03). -/
theorem operation_preserves_memory_unless_write
    (op : OperationClass) (S₁ S₂ : VMStateWith (Index → Value)) (hop : op ≠ .write)
    (h : isa.operation op S₁ S₂) :
    S₂.mem = S₁.mem := by
  cases op <;> simp_all [operation, FullMemory.read]

/-! ## Connection to committed-memory execution -/

/-- Select the PC/register requirements for the instruction at the current
program counter. Both the committed-memory and full-memory checks use this
helper, so they apply the same non-memory requirements. It does not define a
second VM step.

Paper: the fetch condition in `eq:phiop` (ch01). -/
def selectedMemFreePred : MemFreePredicate :=
  fun pc₁ regs₁ pc₂ regs₂ =>
    isa.memFreePred (isa.code pc₁) pc₁ regs₁ pc₂ regs₂

/-- A committed-memory operation selected by the fixed program.

`CommittedMemory.step` checks the opening proof and the change, or lack of
change, to committed memory. The remaining conditions check that the `MemStep`
case matches `code[pc]` and that its address and value come from the designated
registers. In particular, a proof cannot claim a read when the program calls
for a write, or open a different address from the one in the address register.

The explicit `w` argument is necessary here because read and write values carry
the opening proofs later used to reconstruct full memory. The bus layer will
add its own checks to this relation in a later issue.

Paper: `eq:phi-read-decomp`, `eq:phi-write-decomp` (ch01), and the memory
component of `eq:step-bus2` (ch03). -/
def committedOperation {VC : VectorCommitment}
    (isa : System VC.Index VC.Value)
    (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC) : Prop :=
  CommittedMemory.step isa.selectedMemFreePred Ŝ₁ Ŝ₂ w ∧
    match w with
    | .read addr v _ =>
        isa.code Ŝ₁.pc = .read ∧
        addr = isa.indexOfWord (Ŝ₁.regs 0) ∧
        v = isa.valueOfWord (Ŝ₂.regs 1)
    | .write addr v _ _ =>
        isa.code Ŝ₁.pc = .write ∧
        addr = isa.indexOfWord (Ŝ₁.regs 0) ∧
        v = isa.valueOfWord (Ŝ₁.regs 1)
    | .other =>
        isa.code Ŝ₁.pc = .arith ∨
        isa.code Ŝ₁.pc = .hash ∨
        isa.code Ŝ₁.pc = .bin

/-- The relation between two committed states used by a concrete VM. It holds
when there is some `MemStep` satisfying `committedOperation`. Callers of this
relation do not pass the opening proof explicitly, while segment witnesses keep
that proof so memory reconstruction can use it.

Paper: committed step predicate in `eq:step-bus2` (ch03), without the bus
condition deferred to the bus layer. -/
def committedStep {VC : VectorCommitment}
    (isa : System VC.Index VC.Value)
    (Ŝ₁ Ŝ₂ : CommittedVMState VC) : Prop :=
  ∃ w : MemStep VC, isa.committedOperation Ŝ₁ Ŝ₂ w

/-- Suppose a committed operation is accepted and memory reconstruction checks
the same `MemStep` between the corresponding full states. Then those full
states satisfy `stepPlain`. `CommitInv` supplies the fact that each committed
state has the same program counter and registers as its full state.

`TwoStep.System.memoryBridge` uses this theorem to keep opening proofs inside
the extraction argument while making `ZkVM.step` the ordinary fixed-program
execution predicate.

Paper: the committed/full operation correspondence used in
`prop:memory-extractability` and Step 6 of `thm:main` (ch05). -/
theorem committedOperation_stepPlain {VC : VectorCommitment}
    (isa : System VC.Index VC.Value)
    (S₁ S₂ : FullVMState VC) (Ŝ₁ Ŝ₂ : CommittedVMState VC) (w : MemStep VC)
    (hInv₁ : CommitInv Ŝ₁ S₁) (hInv₂ : CommitInv Ŝ₂ S₂)
    (hcommitted : isa.committedOperation Ŝ₁ Ŝ₂ w)
    (hfull : FullMemory.step isa.selectedMemFreePred S₁ S₂ w) :
    isa.stepPlain S₁ S₂ := by
  rw [isa.stepPlain_iff_operation_at_pc]
  obtain ⟨hpc₁, hregs₁, _⟩ := hInv₁
  obtain ⟨_, hregs₂, _⟩ := hInv₂
  obtain ⟨_, hmatches⟩ := hcommitted
  cases w with
  | read addr value proof =>
      obtain ⟨hcode, haddr, hvalue⟩ := hmatches
      rw [hpc₁] at hcode
      rw [hregs₁] at haddr
      rw [hregs₂] at hvalue
      refine ⟨rfl, ?_⟩
      simpa [FullMemory.step, FullMemory.read, selectedMemFreePred,
        hcode, haddr, hvalue] using hfull
  | write addr value oldValue proof =>
      obtain ⟨hcode, haddr, hvalue⟩ := hmatches
      rw [hpc₁] at hcode
      rw [hregs₁] at haddr hvalue
      refine ⟨rfl, ?_⟩
      simpa [FullMemory.step, FullMemory.write, selectedMemFreePred,
        hcode, haddr, hvalue] using hfull
  | other =>
      rcases hmatches with hcode | hcode | hcode
      · rw [hpc₁] at hcode
        refine ⟨rfl, ?_⟩
        simpa [FullMemory.step, selectedMemFreePred, hcode] using hfull
      · rw [hpc₁] at hcode
        refine ⟨rfl, ?_⟩
        simpa [FullMemory.step, selectedMemFreePred, hcode] using hfull
      · rw [hpc₁] at hcode
        refine ⟨rfl, ?_⟩
        simpa [FullMemory.step, selectedMemFreePred, hcode] using hfull

end System
end ISA
end VanillaZkVM
