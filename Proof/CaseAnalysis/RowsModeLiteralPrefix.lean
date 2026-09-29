import Proof.CaseAnalysis.RowsModeLiteralMarks

/-! The original cell flag physically emits the constant member of a
literal pair; its variable member is emitted by the retained index copier. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPrefix
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch CloseoutRowsModeLiteralMarks
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 5 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>decide (q=2)
  rule:=fun q bits=>if q=0 then
    if bits 4 then some ⟨1,fun i=>if i=2 then some true else none,fun i=>if i=2 then .right else .stay⟩
    else some ⟨2,fun _=>none,fun _=>.stay⟩
    else if q=1 then some ⟨2,fun i=>if i=2 then some false else none,fun i=>if i=2 then .right else .stay⟩
    else none

end NearCubicWires.RepairOrdinary.CloseoutRowsModeLiteralPrefix
