import Proof.MachineModel.BankCountLayout
import Proof.MachineModel.BankOptional
import Proof.MachineModel.NativeFanoutLayout

/-! Observed bits and the proved common extent identify the exact native
input lists, so false backing never becomes a prepared-word assumption. -/
namespace NearCubicWires.ExtIncidence.NativeTemplate
open LocalBitMultitape RepairOrdinary RepairOrdinary.RecoveryBoundedTapeCopy
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.NativeTemplate
