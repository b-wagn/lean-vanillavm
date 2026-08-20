import VanillaZkVM.Preliminaries.VectorCommitment

/-!
# VM states (Execution Model — Chapter 1)

The state vocabulary shared by every concrete VM: machine words, byte-addressed
memory, and the Lean structure that groups a program counter, registers, and
memory into one VM state.

These belong to the *VMs*, not to the specification: the abstract `ZkVM` in
`Specification/Zkvm.lean` is parameterized by an opaque `State` type and never
mentions them. Keeping the state vocabulary here is what leaves `Specification/`
free of any dependency on the commitment layer.

## Main definitions
* `Word` / `Addr` / `Byte` — the scalar types (all abstracted as `ℕ` for now).
* `VMStateWith` — the structure containing `pc`, `regs`, and `mem`, with the
  type of `mem` supplied as a parameter.
* `VMState` — the full byte-addressed state `S = (pc, regs, mem)`.
* `CommittedVMState` — the committed state `Ŝ = (pc, regs, mem̂)`.

The commitment-native full state `FullVMState` and the representation relation
`CommitInv` tying the two together live in `Memory.lean`, beside the
reconstruction argument that uses them.
-/

namespace VanillaZkVM

/-- A 32-bit machine word (abstracted as `ℕ` for now). -/
abbrev Word : Type := ℕ
/-- A byte-addressed memory address. -/
abbrev Addr : Type := ℕ
/-- A byte stored in memory. -/
abbrev Byte : Type := ℕ

/-- A VM state parameterized by its memory representation `Mem`. The register
file is modeled as a total function from a register index to its word value.

Paper: ch01, section “Program, Execution, and VM State.” -/
structure VMStateWith (Mem : Type) where
  pc : Word
  regs : ℕ → Word
  mem : Mem

/-- Full VM state `S = (pc, regs, mem)` with explicit byte-addressed memory.

This is the ordinary state described in the paper: addresses have type `Addr`
and stored values have type `Byte`. It is still useful even though the memory
proofs allow other address and value types. `FullVMState VC` in `Memory.lean`
uses the same `VMStateWith` structure with the types chosen by `VC`. Thus both
names describe states with the same three fields; `VMState` is the form whose
memory has the paper's `Addr → Byte` type.

Paper: ch01, section “Program, Execution, and VM State.” -/
abbrev VMState : Type := VMStateWith (Addr → Byte)

/-- Committed VM state `Ŝ = (pc, regs, mem̂)`: memory replaced by a commitment.

Paper: ch02, section “Execution Segments,” and ch03 `eq:step-bus2`. -/
abbrev CommittedVMState (VC : VectorCommitment) : Type := VMStateWith VC.Com

end VanillaZkVM
