import Proof.CaseAnalysis.RowsTouchingFrameStream
import Proof.MachineModel.FrameSkip
import Proof.MachineModel.Runs

/-! The shared seek copies or skips an original framed field without
interpreting its payload. Both modes consume exactly the same source bytes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
open LocalBitMultitape RecoveryExecution RecoveryRootRound ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def frameMachine (keep : Bool) : Machine 2 3 :=
  if keep then CloseoutRowsTouching.FrameStream.machine else TapeEmbedding.machine 1 FrameSkip.machine


end NearCubicWires.RepairOrdinary.CloseoutRowsTupleSeek
