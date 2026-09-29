import Proof.CaseAnalysis.RowsOriginalTemplates
import Proof.CaseAnalysis.RowsProjectionReset
import Proof.MachineModel.Layout

/-! The source's SAME cached PCPP clause query feeds the actual signed-pair
parser. No original proof-coordinate stream is supplied separately. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound RepairRepresentation SourceInterfaces
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def index {n : ℕ} (l : Literal n):=(ComponentwiseBranchExtraction.literalIndex l).val
def negative {n : ℕ} (l : Literal n):=ComponentwiseBranchExtraction.literalNegated l


end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalClause
