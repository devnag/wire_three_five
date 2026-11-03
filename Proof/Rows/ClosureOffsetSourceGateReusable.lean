import Proof.Rows.ClosureOffsetSourceGate

/-! Exact reusable native gate evaluator. The retained masters contain only
the original native source, assignment, dimensions and zero workspace; the
computed gate bit is appended and all other tapes are restored literally. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OffsetSourceGate
open LocalBitMultitape RepairOrdinary RecoveryRootRound ExtDecompositionBatch
open RepairRepresentation RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsPoolWeight

def extra : Fin 4→List Bool := ![[],[],CompareMachine.word 0,[]]
noncomputable def worker := TapeEmbedding.machine 4 core
noncomputable def machine := Reusable48.machine worker

end NearCubicWires.P1Closure.OffsetSourceGate
