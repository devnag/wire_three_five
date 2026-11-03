import Proof.CaseAnalysis.FinalRowScannerDock
import Proof.CaseAnalysis.RowsEstimatorBacking
import Proof.CaseAnalysis.RowsEstimatorPrepareLive
import Proof.CaseAnalysis.RowsEstimatorPreparedPorts
import Proof.CaseAnalysis.FinalRowFrameJoin

/-! A reused, common-capacity row transaction: copy the seven produced fields,
then execute the actual warm printer, append and reset. The native header can
remain padded to C throughout. Field production and the scanner remain explicit
upstream work; this theorem does not assume that an arbitrary scratch bank
contains either. -/
namespace NearCubicWires.P1Independent.WarmTransaction
open LocalBitMultitape RepairRepresentation RepairOrdinary ExtDecompositionBatch
open RepairOrdinary.CloseoutRowsEstimator RepairOrdinary.C10RowFrameJoin
open RepairOrdinary.MatrixScoreBatch
open RepairOrdinary.CompetitorSelectedCount RepairOrdinary.CompetitorCountMask
open RepairOrdinary.CloseoutRowsEstimatorCoefficients
open RepairOrdinary.CompetitorCrossScheduler (producer)
open RepairSource.CloseoutFinal
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

attribute [local irreducible] Warm.machine Warm.input WarmFields.words
  CompetitorCrossScheduler.producer

noncomputable def machine (a : WilliamsAlgorithm) :=
  Composition.machine (WarmPrepare.copy (producer a))
    (TapeEmbedding.machine 7 (WarmActual.machine a))

end NearCubicWires.P1Independent.WarmTransaction
