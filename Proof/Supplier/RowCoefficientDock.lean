import Proof.Supplier.RowCoefficientLoopReset

/-! The actual loop endpoint supplies the seven normalization tapes. The
same normalizer accepts the physically retained zero padding in its flag
and magnitude slots; only its two output tapes are fresh. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientDock
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 7 → Fin 28 := ![10,11,19,16,25,26,27]

end NearCubicWires.RepairOrdinary.RowCoefficientDock
