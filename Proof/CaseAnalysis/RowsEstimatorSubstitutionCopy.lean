import Proof.CaseAnalysis.RowsEstimatorSubstitutionEraseReset

/-! One logical polynomial copy either restores the accumulator or appends
to the live output. Its cost is independent of padding and output prefix. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCopy
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (reset : Bool) (i : Fin 5) : Bool:=decide (i=0) || (reset && decide (i=2))
noncomputable def machine (reset : Bool):=MaskedReset.machine CloseoutRowsRawPolynomialAdd.machine (selected reset)

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionCopy
