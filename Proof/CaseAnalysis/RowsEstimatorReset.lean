import Proof.CaseAnalysis.CloseoutRowsEstimatorRetained
import Proof.CaseAnalysis.RowsProjectionReset

/-! Reuse the estimator's private bank with physically supplied D backing.
The native cut tape is external and enters at a nonzero append cursor, so
it is deliberately excluded from the zero-head reset and support claims.
D is separate from native C: the initial paid C rewind itself costs 2C+2. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
open LocalBitMultitape RepairRepresentation
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (p : Program) (i : Fin (WholePrefix.tapes p)):=decide (i.val≠52)
def caps (p : Program) (D : ℕ) (i : Fin (WholePrefix.tapes p)):=if i.val=52 ∨ i.val=68 then 0 else D
noncomputable def machine (a : WilliamsAlgorithm):=MaskedReset.machine (Whole.machine a) (selected (producer a))
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C D Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool):=
  ZeroPadding.config (Rewind.Workspace.capacities (WholePrefix.tapes (producer a)) (D+1))
    (Rewind.recording (ZeroPadding.config (caps (producer a) D)
      (Whole.entry a row C Q q denominator select)) 0)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Reset
