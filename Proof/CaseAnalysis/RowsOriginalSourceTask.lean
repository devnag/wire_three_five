import Proof.CaseAnalysis.CaseTwoMetadata
import Proof.CaseAnalysis.CaseTwoVariablePrep
import Proof.CaseAnalysis.RowsOriginalClause
import Proof.CaseAnalysis.RowsOriginalTask

/-! One ordinary source-backed action reads the original clause and
executes its selected fixed template, producing exact original-term tuples. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSourceTask
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound SourceInterfaces RepairRepresentation
open CloseoutRowsOriginalClause CloseoutRowsOriginalMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def control {n : ℕ} (S : ℕ) (p : TwoLiteralClause n) : Fin 4→Bool:=
  ![negative p.left,negative p.right,decide (S ≤ index p.left),decide (S ≤ index p.right)]

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSourceTask
