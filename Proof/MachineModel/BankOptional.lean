import Proof.CaseAnalysis.WitnessHeaderSwitch
import Proof.MachineModel.BankZero

/-! One actual raw stream runs through the positive or empty bank entry.
The caller supplies the existing native ports; no separate marker, count pass
or serialized polynomial packet is required. -/
namespace NearCubicWires.ExtIncidence.BankOptional
open LocalBitMultitape RepairOrdinary BankConsumer
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

end
end NearCubicWires.ExtIncidence.BankOptional
