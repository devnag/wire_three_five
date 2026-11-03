import Proof.CaseAnalysis.RowsEstimatorWholePrefix
import Proof.CaseAnalysis.RowsEstimatorRecord

/-! One shared physical estimator from actual native cut bytes at their
append cursor. The original row/Williams full table runs before the selected
SUM. The live metadata producers remain explicit in the input bank. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Whole
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask
open CompetitorCrossScheduler (producer)
open CloseoutRowsEstimatorCoefficients
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def callee (a : WilliamsAlgorithm):=
  CloseoutRowsRawRecord.machine (producer a) (CompetitorCountTableRecord.machine a)
noncomputable def machine (a : WilliamsAlgorithm):=WholePrefix.machine (producer a) (callee a)
noncomputable def entry (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool):=
  WholePrefix.entry (producer a) (callee a) row C (Record.input (producer a) row Q q denominator select)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (C Q : ℕ):=
  Cold.budget row C+1+CloseoutRowsRawRecord.budget a row Q
def recordSlot (p : Program):=WholePrefix.slots p (CloseoutRowsRawRecord.receive p (CompetitorCountTableRecord.slots p 117))
def matrixSlot (p : Program):=WholePrefix.slots p (CloseoutRowsRawRecord.receive p (CompetitorCountTableRecord.slots p 0))

theorem source (p : Program) (row : EquationRow.Input) (Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool)
    (i : Fin (CloseoutRowsRawRecord.tapes p)) (hi:i.val=0) :
    Record.input p row Q q denominator select i=frame (EquationRowRaw.source row):=by
  have he:i=(0 : Fin 130).castAdd (CompetitorCountTableRecord.tapes p):=Fin.ext hi
  rw [he]
  rfl

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Whole
