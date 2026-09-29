import Proof.Packets.PacketsSetupDriver

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.PacketsGlue.Nest
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch

end NearCubicWires.PacketsGlue.Nest

namespace NearCubicWires.PacketsGlue.DriverPhase
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue.CeilSqrt (sentC)
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.RecoveryRootRound

/-! ## Slots -/


/-! ## The machine and its banks -/

end NearCubicWires.PacketsGlue.DriverPhase

