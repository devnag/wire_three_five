import Proof.CaseAnalysis.RowsTupleSeekFrame
import Proof.MachineModel.Layout

/-! One physical bottom-count driver advances the native and declared
support streams together, including the empty bottom list. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

abbrev GatePair := List Bool × List Bool
def nativeWord (gs : List GatePair) := gs.flatMap (fun g=>frame g.1)
def supportWord (gs : List GatePair) := gs.flatMap (fun g=>frame g.2)

end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
