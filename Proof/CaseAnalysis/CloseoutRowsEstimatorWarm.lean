import Proof.CaseAnalysis.RowsEstimatorScanned

/-! The original header/framer and row/Williams remainder start directly
from the paid scanner endpoint. This is the consumer after D allocation;
the exact scanner output replaces no source, count or table computation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Warm
open LocalBitMultitape MatrixScoreBatch RepairRepresentation
open CompetitorSelectedCount CompetitorCountMask CloseoutRowsEstimatorCoefficients
open CompetitorCrossScheduler (producer)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def headerSlots (p : Program) (i : Fin 59) : Fin (WholePrefix.tapes p):=
  (Framed.slots i).castAdd 2 |>.castAdd (CloseoutRowsRawRecord.tapes p)
noncomputable def first (p : Program):=RecoveryFocus.machine (headerSlots p) Header.framed
noncomputable def core {s : ℕ} (p : Program) (callee : Machine (CloseoutRowsRawRecord.tapes p) s):=
  Composition.machine (first p) (WholePrefix.last p callee)
noncomputable def machine (a : WilliamsAlgorithm):=core (producer a) (Whole.callee a)
noncomputable def supplied (p : Program) (row : EquationRow.Input) (C : ℕ)
    (data : Fin (CloseoutRowsRawRecord.tapes p)→List Bool) :=
  Fin.addCases (m:=70) (n:=CloseoutRowsRawRecord.tapes p) (motive:=fun _=>List Bool)
    (Scanned.output row C) (WholePrefix.extra p data)
noncomputable def input (p : Program) (row : EquationRow.Input) (C Q : ℕ)
    (q : CompetitorValidity.Estimate) (denominator : ℕ)
    (select : Fin (EquationRow.request row).U→Fin (EquationRow.request row).U→Bool) :=
  supplied p row C (Record.input p row Q q denominator select)
noncomputable def budget (a : WilliamsAlgorithm) (row : EquationRow.Input) (Q : ℕ):=
  Header.framedBudget row+1+CloseoutRowsRawRecord.budget a row Q

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Warm
