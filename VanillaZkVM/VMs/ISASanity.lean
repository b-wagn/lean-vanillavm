import VanillaZkVM.VMs.ISA
import VanillaZkVM.Specification.Zkvm

/-!
# Sanity checks for the representative ISA operation classes

These private examples demonstrate both accepted and rejected steps. They cover
an accepted read, an accepted write whose output memory differs from its input,
rejection when the program contains a different operation class, and rejection
when a write produces the wrong memory. A private `ZkVM` instance also checks
that `ISA.System.stepPlain` can be used directly as its `step` field.

Nothing in this file adds to the public API or asserts concrete cryptographic
security.
-/

namespace VanillaZkVM
namespace ISASanity

private def systemFor (op : ISA.OperationClass) : ISA.System Addr Byte where
  code := fun _ => op
  memFreePred := fun _ _ _ _ _ => True
  indexOfWord := id
  valueOfWord := id

private def zeroState : VMState :=
  ⟨0, fun _ => 0, fun _ => 0⟩

private theorem accepts_read :
    (systemFor .read).stepPlain zeroState zeroState := by
  simp [ISA.System.stepPlain, ISA.System.operation, systemFor,
    FullMemory.read, zeroState]

private def writeRegisters (i : ℕ) : Word :=
  if i = 1 then 1 else 0

private def writeMemory (i : Addr) : Byte :=
  if i = 0 then 1 else 0

private def beforeWrite : VMState :=
  ⟨0, writeRegisters, fun _ => 0⟩

private def afterWrite : VMState :=
  ⟨0, writeRegisters, writeMemory⟩

private theorem accepts_changed_write :
    (systemFor .write).stepPlain beforeWrite afterWrite := by
  simp [ISA.System.stepPlain, ISA.System.operation, systemFor,
    FullMemory.write, beforeWrite, afterWrite, writeRegisters, writeMemory]

private theorem rejects_wrong_fetch :
    ¬(systemFor .write).operation .read zeroState zeroState := by
  simp [ISA.System.operation, systemFor]

private theorem rejects_incorrect_write_result :
    ¬(systemFor .write).operation .write beforeWrite beforeWrite := by
  simp [ISA.System.operation, systemFor, FullMemory.write, beforeWrite,
    writeRegisters]

private def readZkVM : ZkVM where
  State := VMState
  step := (systemFor .read).stepPlain
  T := 1
  Stmt := VMState × VMState
  initial := Prod.fst
  terminal := Prod.snd
  Proof := Unit
  verify := fun x _ => (systemFor .read).stepPlain x.1 x.2

private theorem concrete_zkVM_uses_stepPlain :
    readZkVM.step zeroState zeroState :=
  accepts_read

end ISASanity
end VanillaZkVM
