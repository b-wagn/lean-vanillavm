import VanillaZkVM.Zkvm

/-!
# Demo:
  1) keep `CTE` as is
  2) introduce two dummy VMs with two different assumption families
  3) show how CTE can be proven for them.
-/

namespace VanillaZkVM
namespace Demo

open Reduction ZkVM

/-! ## VM 1: `VanillaVM` — trusts bus collision resistance and update binding -/

section Vanilla

variable (Hbus : HashCommitment) (k : Hbus.Key) (VC : VectorCommitment)

/-- The family of assumptions for VanillaVM. -/
def VanillaVMAssumptions : AssumptionFamily :=
  .ofList [crAssumption Hbus k, updAssumption VC]

variable (VanillaVM : ZkVM)

/-- Headline: if the assumption family holds, `CTE` follows
 --
 -- Once a concrete VM proves its reduction, `hred` disappears and the
 -- headline shrinks to `(hA : ….Holds) → CTE`. -/
theorem vanillaVM_cte
    (hred : ReducesToFamily VanillaVM.ASstar (VanillaVMAssumptions Hbus k VC))
    (hA : (VanillaVMAssumptions Hbus k VC).Holds) :
    VanillaVM.CTE :=
  cte_of_reducesTo hred hA

end Vanilla

/-! ## VM 2: `FlockVM` — trusts update binding and position binding -/

section Flock

variable (VC : VectorCommitment)

/-- The family of assumptions for FlockVM. -/
def FlockVMAssumptions : AssumptionFamily :=
  .ofList [updAssumption VC, posAssumption VC]

variable (FlockVM : ZkVM)

/-- cte theorem for FLOCK -/
theorem flockVM_cte
    (hred : ReducesToFamily FlockVM.ASstar (FlockVMAssumptions VC))
    (hA : (FlockVMAssumptions VC).Holds) :
    FlockVM.CTE :=
  cte_of_reducesTo hred hA

end Flock

end Demo
end VanillaZkVM
