import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterLayout

/-! Execute one complete original monomial and append its raw substituted body. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def body:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (Composition.machine init advance) inner) advance) append) clear

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
