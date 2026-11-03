import Proof.Rows.RowsRowLevelFields
import Proof.CaseAnalysis.RowsEstimatorScanRun
import Proof.Hierarchy.CompetitorRecordRewind
import Proof.MachineModel.ClockUnaryProduct
import Proof.PCP.ProjectionRawFrame
import Proof.Rows.Plan

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsRowLevel
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open CompetitorCrossScheduler (producer)
attribute [local irreducible] CompetitorCrossScheduler.producer P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The transducer docked at arbitrary ports -/

/-! ## 2. The eleven transducer outputs are eleven datum fields, framed -/

/-! ## 3. The docked transducer at the thirteen field slots -/


end
end RowsRowLevel
