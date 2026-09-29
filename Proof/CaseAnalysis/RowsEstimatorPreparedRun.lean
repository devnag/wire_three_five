import Proof.CaseAnalysis.RowsEstimatorPrepareWords

/-! Execute paid preparation and the actual original Warm/reset/append consumer. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def last (a : WilliamsAlgorithm):=TapeEmbedding.machine 7 (WarmActual.machine a)
noncomputable def machine (a : WilliamsAlgorithm):=Composition.machine (WarmPrepare.machine (producer a)) (last a)

noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  4*Driver.value a row.d row.p row.cuts.length C+9+1+WarmActual.budget a row C Q


end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmPrepared
