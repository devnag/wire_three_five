import Proof.Amplification.RecoveryProjectionCapacity
import Proof.Amplification.RecoveryProjectionInitialize

/-! Full scalar-to-row preparation. The only initial data are the original
binary R/Q fields and query source bytes. Actual unary parsing, polynomial
capacity generation, allocation, randomness writes and head moves are paid. -/
namespace NearCubicWires.RepairSource.RecoveryProjectionScalar
open LocalBitMultitape RepairOrdinary RecoveryExecution RecoveryRootRound RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairSource.RecoveryProjectionScalar
