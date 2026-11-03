import Proof.CaseAnalysis.CloseoutRowsEstimatorPaidWarmJoin

/-! The actual allocated driver and reusable original estimator run in one bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def warm (a : WilliamsAlgorithm):=
  TapeEmbedding.machine (ScannedClean.tapes a) (WarmPrepared.machine a)
noncomputable def warmMachine (a : WilliamsAlgorithm):=Composition.machine (driver a) (warm a)
noncomputable def warmEntry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U → Fin (EquationRow.request row).U → Bool) (out : List Bool):=
  WarmPrepared.startWith (driver a) (warm a) (heads a (producer a) out)
    (input a (producer a) row C (WarmFields.words row Q q denominator select) out)
noncomputable def warmBudget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  ScannedClean.budget a row C+1+WarmPrepared.budget a row C Q

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
