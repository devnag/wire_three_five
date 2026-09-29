import Proof.Packets.WalkRawSegment

/-! Determine the low padding bit from the actual rank tape and skip it.
The rank tape and source word are retained. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedPadding
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def machine : Machine 2 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q bits=>if q.val<2 then some (if bits 0 then
      ⟨if q.val=0 then 1 else 0,fun _=>none,![.right,.stay]⟩ else
      ⟨2,fun _=>none,![.left,if q.val=0 then .right else .stay]⟩)
    else if q.val=2 then some (if bits 0 then
      ⟨2,fun _=>none,![.left,.stay]⟩ else
      ⟨3,fun _=>none,![.right,.stay]⟩) else none


end Theorem25Completion.WalkSeedPadding
