import Proof.CaseAnalysis.RowsEstimatorSubstitutionRepeat
import Proof.CaseAnalysis.RowsOriginalFactor

/-! Each original family index block controls one actual single-cache Cartesian operation. No repeated factor is cancelled. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawAtomSeek CloseoutRowsEstimator
open SubstitutionFactor (data heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=SubstitutionRepeat.machine CloseoutRowsOriginalFactor.machine 0

end NearCubicWires.RepairOrdinary.CloseoutRowsOriginalMonomial
