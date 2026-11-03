import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterBody

/-! Original monomial delimiters control the polynomial substitution loop. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def loop:=SubstitutionRepeat.machine body 0

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
