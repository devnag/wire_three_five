import Proof.CaseAnalysis.RowsModeCacheLoop

/-! The cache source starts at the original head-zero boundary. Three
actual steps write the constant unary index one and enter the retained
population and two empty counters. No caller supplies a literal-cache pair. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryExecution RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def initMachine : Machine 25 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=3)
  rule:=fun q _=>if h:q.val<3 then some ⟨⟨q.val+1,by omega⟩,
    fun i=>if i=18 then some (decide (q=1)) else none,
    fun i=>if i=18 then (if q=2 then .left else .right)
      else if q=0 ∧ (i=19 ∨ i=23 ∨ i=24) then .right else .stay⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
