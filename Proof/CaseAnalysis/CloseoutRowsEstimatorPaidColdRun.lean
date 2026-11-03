import Proof.CaseAnalysis.RowsEstimatorPaidRetireJoin

/-! The original native append input reaches the scalar consumer through
the mandatory scan, actual D allocation, paid copies, Warm and retirement. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def retiredMachine (a : WilliamsAlgorithm):=Composition.machine (warmMachine a) (retire a (producer a))
noncomputable def bound (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  Scanned.budget row C+1+(ScannedClean.budget a row C+1+
    (8*Driver.value a row.d row.p row.cuts.length C+40*scalarWidth (EquationRow.request row) Q+74)+
    1+(2*Driver.value a row.d row.p row.cuts.length C+4))

theorem nested_start {n s t u : ℕ} (first : Machine n s) (second : Machine n t)
    (third : Machine n u) (H : Fin n → ℕ) (A : Fin n → List Bool) :
    Composition.leftConfig u (WarmPrepared.startWith first second H A)=
      (⟨(Composition.machine (Composition.machine first second) third).start,H,A⟩ : Configuration n (s+t+u)) := rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Paid
