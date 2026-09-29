import Proof.MachineModel.ClosureRawRowJoin

/-! Actual scanner/printer → binary row payload, with a restored bounded
record buffer. This consumes the preceding joins at one physical bank.
Native header, metadata, mask and paid workspace are still produced upstream.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ScannedRawRow
open LocalBitMultitape ExtDecompositionBatch RepairRepresentation RepairOrdinary
open CloseoutRowsEstimator CloseoutRowsEstimatorCoefficients C10RowFrameJoin RecoveryRootRound
open CompetitorSelectedCount CompetitorCountMask MatrixScoreBatch
open CompetitorCrossScheduler (producer)
open RepairSource.CloseoutFinal P1Independent

attribute [local irreducible] CompetitorCrossScheduler.producer Warm.input

def port (p : Program) : Fin (ScannedRow.tapes p) := ((Reuse.output p).castAdd 7).castAdd 3

noncomputable def machine (a : WilliamsAlgorithm) :=
  RawRowJoin.machine (ScannedRow.machine a) (port (producer a))

end NearCubicWires.P1Closure.ScannedRawRow
