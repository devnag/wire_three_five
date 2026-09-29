import Proof.MachineModel.NativeRound

/-! Canonical reusable states change only the source and append positions.
Every other ambient tape is the same actual initialized workspace. -/
namespace NearCubicWires.ExtIncidence.NativeState
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch NativeFanoutLayout
open RepairOrdinary.RecoveryRootRound NativeInitialize NativeInitializedPorts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.ExtIncidence.NativeState
