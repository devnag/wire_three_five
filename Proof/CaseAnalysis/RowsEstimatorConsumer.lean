import Proof.CaseAnalysis.RowsEstimatorHeader

/-! The existing raw-row/Williams prefix with literal caller metadata.
Only the original physical request is supplied at bank zero; its actual
count-table consumer remains responsible for producing every count byte. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Consumer
open LocalBitMultitape MatrixScoreBatch
open CloseoutRowsRawRecord (tapes receive receive_injective first last machine)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def extra (p : Program) (data : Fin (CompetitorCountTableRecord.tapes p)→List Bool)
    (i : Fin (CompetitorCountTableRecord.tapes p)):=if i.val=0 then [] else data i
def input (p : Program) (row : EquationRow.Input)
    (data : Fin (CompetitorCountTableRecord.tapes p)→List Bool):=
  fun i=>Fin.addCases (m:=130) (n:=CompetitorCountTableRecord.tapes p) (motive:=fun _=>List Bool)
    (EquationRowFramed.input row) (extra p data) i

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.Consumer
