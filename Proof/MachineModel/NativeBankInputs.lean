import Proof.MachineModel.NativeTemplateExact
import Proof.MachineModel.NativeInitializedPorts

/-! The physically initialized bank supplies all native, count-conversion
and raw-incidence inputs, without an input row count or last-index word. -/
namespace NearCubicWires.ExtIncidence.NativeBankInputs
open LocalBitMultitape RepairOrdinary NativeInitializedPorts NativeFanoutLayout
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

end NearCubicWires.ExtIncidence.NativeBankInputs
