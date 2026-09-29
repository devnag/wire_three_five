import Proof.MachineModel.Transaction

/-! Paper A.3/C.10: one paid scanner, metadata copy, native row computation,
record append and reset, at one common capacity. The inputs are the produced
header, three scanner fields and seven estimator fields. No answer stream is
an input. The complete exit bank is retained for the next row's producer.
-/

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.P1Closure.ScannedRow
open LocalBitMultitape RepairRepresentation RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.CloseoutRowsEstimator RepairOrdinary.C10RowFrameJoin
open RepairOrdinary.RecoveryRootRound RepairOrdinary.MatrixScoreBatch
open RepairOrdinary.CompetitorSelectedCount RepairOrdinary.CompetitorCountMask
open RepairOrdinary.CloseoutRowsEstimatorCoefficients
open RepairOrdinary.CompetitorCrossScheduler (producer)
open RepairSource.CloseoutFinal P1Independent

attribute [local irreducible] Warm.machine Warm.input WarmFields.words
  CompetitorCrossScheduler.producer install dockH

def tapes (p : Program) := (Reuse.tapes p+7)+3
def scanSlots (p : Program) : Fin (Reuse.tapes p+3) → Fin (tapes p) :=
  Fin.addCases (fun j => (j.castAdd 7).castAdd 3)
    (fun j => j.natAdd (Reuse.tapes p+7))

noncomputable def scanner (p : Program) :=
  RecoveryFocus.machine (scanSlots p)
    (RecoveryFocus.machine (C10RowScannerDock.slots p) C10RowScannerReload.machine)
noncomputable def machine (a : WilliamsAlgorithm) :=
  Composition.machine (scanner (producer a))
    (TapeEmbedding.machine 3 (WarmTransaction.machine a))

end NearCubicWires.P1Closure.ScannedRow
