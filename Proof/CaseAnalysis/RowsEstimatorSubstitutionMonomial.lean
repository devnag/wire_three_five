import Proof.CaseAnalysis.RowsEstimatorSubstitutionRepeat
import Proof.CaseAnalysis.RowsEstimatorSubstitutionFactorRun

/-! Each original factor block controls one actual reusable Pair operation. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
open SubstitutionFactor (data heads)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=SubstitutionRepeat.machine SubstitutionFactor.machine 0

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionMonomial
