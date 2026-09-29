import Proof.CaseAnalysis.RowsEstimatorReuse
import Proof.CaseAnalysis.RowsEstimatorReuseRetained

/-! Actual shared estimator consumer after scanner/driver preparation.
The chosen D discharges runtime and every literal input-support bound;
its ordinary driver and metadata producers must fill the stated entry. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open RepairSource.RecoveryTseitinReadOnly
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine (a : WilliamsAlgorithm):=WarmReuse.machine (producer a) (Warm.machine a)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  Reuse.budget (Warm.budget a row Q) (scalarWidth (EquationRow.request row) Q)
    (Driver.value a row.d row.p row.cuts.length C)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.WarmActual
