import VanillaZkVM.Preliminaries.VectorCommitment

/-!
# VM states (Execution Model — Chapter 1)

The state vocabulary shared by every concrete VM: machine words, byte-addressed
memory, and the state record in its full-memory and committed-memory forms.

These belong to the *VMs*, not to the specification: the abstract `ZkVM` in
`Specification/Zkvm.lean` is parameterized by an opaque `State` type and never
mentions them. Keeping the state vocabulary here is what leaves `Specification/`
free of any dependency on the commitment layer.

## Main definitions
* `Word` / `Addr` / `Byte` — the scalar types (all abstracted as `ℕ` for now).
* `VMStateWith` — the state record, parameterized by its memory representation.
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

/-- A VM state parameterized by its memory representation `Mem`. The `k`
registers are abstracted as a total function `index ↦ value`.

Paper: ch01, section “Program, Execution, and VM State.” -/
structure VMStateWith (Mem : Type) where
  pc : Word
  regs : ℕ → Word
  mem : Mem

/-- Full VM state `S = (pc, regs, mem)` with explicit byte-addressed memory.

Paper: ch01, section “Program, Execution, and VM State.” -/
abbrev VMState : Type := VMStateWith (Addr → Byte)

/-- Committed VM state `Ŝ = (pc, regs, mem̂)`: memory replaced by a commitment.

Paper: ch02, section “Execution Segments,” and ch03 `eq:step-bus2`. -/
abbrev CommittedVMState (VC : VectorCommitment) : Type := VMStateWith VC.Com

end VanillaZkVM
