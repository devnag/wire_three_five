import Proof.CaseAnalysis.RowsEstimatorSubstitutionErase

/-! Return the logical eraser to its reusable zero backing, at logical cost. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def reset:=MaskedReset.machine machine (fun _=>true)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionErase
