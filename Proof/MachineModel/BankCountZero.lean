import Proof.MachineModel.BankCountRaw

/-! The existing zero-polynomial worker uses the same enlarged bank and
leaves every private converter tape untouched. -/
namespace NearCubicWires.ExtIncidence.BankCount
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def zero:=RecoveryFocus.machine rawOld BankZero.machine

end NearCubicWires.ExtIncidence.BankCount
