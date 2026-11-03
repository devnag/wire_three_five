import Proof.CaseAnalysis.RowsEstimatorSubstitutionEraseReset
import Proof.CaseAnalysis.RowsRawProductLoop

/-! Raw multiplication returns both live polynomial heads. Its row capacity
is a proof bound on false logs, independent of the left table length. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionProduct
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawProductLoop.machine (fun i=>decide (i=0 ∨ i=2))

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionProduct
