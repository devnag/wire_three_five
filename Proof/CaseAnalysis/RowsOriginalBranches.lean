import Proof.CaseAnalysis.RowsEstimatorCoefficientsRequest
import Proof.CaseAnalysis.RowsOriginalMonomialRun
import Proof.CaseAnalysis.RowsOriginalSwitch
import Proof.CaseAnalysis.RowsOriginalTemplateSlots
import Proof.CaseAnalysis.RowsTupleSeekPairs

/-! Native sign and auxiliary flags select the exact fixed paper template.
All branches execute the same original-term product and metadata pipeline. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBranches
open LocalBitMultitape ExtDecompositionBatch CloseoutRowsOriginalTemplates CloseoutRowsRawAtomSeek
open CloseoutRowsOriginalMonomial
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalBranches
