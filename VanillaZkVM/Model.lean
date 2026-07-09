-- This file goes at `VanillaZkVM/VanillaZkVM/Model.lean`.

import Mathlib

/-!
# VM states (Execution Model — Chapter 1)

We model the VM state `S = (pc, regs, mem)` and its committed counterpart
`Ŝ = (pc, regs, mem̂)`. Both share the `pc`/`regs` structure and differ only in
how memory is represented, so we factor them through a single structure
`VMStateWith` parameterized by the memory representation.

For this first pass words, addresses and bytes are all `ℕ`. We do **not** yet
enforce the 32-bit range; that is the job of the range-check predicates
introduced in stage 2. Keeping them as `ℕ` avoids modular-arithmetic overhead
while we get the overall structure in place.
-/

namespace VanillaZkVM

/-- A 32-bit machine word (abstracted as `ℕ` for now). -/
abbrev Word : Type := ℕ

/-- A byte-addressed memory address (abstracted as `ℕ`). -/
abbrev Addr : Type := ℕ

/-- A byte stored in memory (abstracted as `ℕ`). -/
abbrev Byte : Type := ℕ

/-- A VM state, parameterized by the representation `Mem` of its memory.

The `k` registers of the document are abstracted as a total function
`index ↦ value`; only finitely many indices are meaningful, but leaving the
register file total makes indexing (`regs 0`, `regs 1`, …) and equality
reasoning painless. -/
structure VMStateWith (Mem : Type) where
  pc : Word
  regs : ℕ → Word
  mem : Mem

/-- Full VM state `S = (pc, regs, mem)` with explicit byte-addressed memory. -/
abbrev VMState : Type := VMStateWith (Addr → Byte)

/-- A binary predicate on states of type `σ` (e.g. a step predicate
`φ(S₁, S₂)`). The concrete operation predicates `φ_op` and the step predicate
`φ_step` are defined in stage 2. -/
abbrev StatePred (σ : Type) : Type := σ → σ → Prop

/-- Memory update `mem[addr ↦ v]`, used by the write predicate. -/
def memUpdate (m : Addr → Byte) (addr : Addr) (v : Byte) : Addr → Byte :=
  Function.update m addr v

end VanillaZkVM
