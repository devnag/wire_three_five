import Proof.Rows.RowState

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
attribute [local irreducible] CompetitorCrossScheduler.producer
noncomputable section

variable (printer : WilliamsAlgorithm)

/-! ## 1. The thirteen field ports of the Frame payload -/

/-! ## 2. `datumFields` at every payload port -/

variable (d : P1TopDownPaidReusable.Datum)

/-! ## 3. The Frame input bank of `complete`'s exit -/

attribute [local irreducible] P1TopDownPaidPayload.tapes


end
end RowsRowLevel
