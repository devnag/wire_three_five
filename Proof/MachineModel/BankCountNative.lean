import Proof.Hierarchy.HierarchyAllocation
import Proof.MachineModel.BankCountLayout
import Proof.MachineModel.BankOptional

/-! Discharge the native worker's row-dependent input from the actual table
and counted index. Every other native input is the same empty-row template. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 113) : Fin 128:=i.castAdd 15

end NearCubicWires.ExtIncidence.BankCount
