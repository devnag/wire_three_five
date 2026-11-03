import Proof.CaseAnalysis.RowsEstimatorSubstitutionOuterLoop

/-! The actual reusable substitution appends one complete terminated polynomial. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsRawPairSeek
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def finish : Machine 11 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun i=>if i=10 then some false else none,
    fun i=>if i=10 then .right else .stay⟩ else none
noncomputable def machine:=Composition.machine loop finish

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimator.SubstitutionOuter
