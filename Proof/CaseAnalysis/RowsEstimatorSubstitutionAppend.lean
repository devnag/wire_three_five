import Proof.CaseAnalysis.RowsEstimatorSubstitutionEraseReset
import Proof.Hierarchy.HierarchyFixedWord

/-! Append one substituted monomial's raw body and initialize its next unit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionAppend
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def machine:=MaskedReset.machine CloseoutRowsRawProductRow.machine (fun i=>decide (i=1))

def unitMachine:=HierarchyFixedWord.machine [true,false,false]

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionAppend
