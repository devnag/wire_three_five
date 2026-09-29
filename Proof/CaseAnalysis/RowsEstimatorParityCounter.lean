import Proof.CaseAnalysis.RowsEstimatorDriverPorts
import Proof.CaseAnalysis.RowsEstimatorParityThreshold

/-! Increment the retained original coordinate or staircase index without allocating a reset log. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Counter
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bs=>if q=0 then some (if bs 0 then ⟨0,fun _=>none,fun _=>.right⟩
      else ⟨1,fun _=>some true,fun _=>.left⟩)
    else if q=1 then some (if bs 0 then ⟨1,fun _=>none,fun _=>.left⟩
      else ⟨2,fun _=>none,fun _=>.right⟩)
    else none

end NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorParity.Counter
