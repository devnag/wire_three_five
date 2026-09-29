import Proof.CaseAnalysis.RowsModeCacheSelect

/-! The actual ordered literal pair append advances its own unary index and
masked count. The original hash label is advanced by the following stage. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def pairMachine:=RecoveryFocus.machine pairSlots CloseoutRowsModeLiteralPair.machine

def cursorMachine : Machine 24 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=1)
  rule:=fun q _=>if q=0 then some ⟨1,fun _=>none,
    fun i=>if i=16 then .left else if i=11 then .right else .stay⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsModeCache
