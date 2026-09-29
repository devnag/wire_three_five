import Proof.Packets.WalkUnframe

/-! Copy a raw bit segment with an actual unary driver. A noninitial driver
position permits the upper Toeplitz diagonal to have one fewer bit. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkRawSegment
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def machine : Machine 3 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bits=>if q.val=0 then some (if bits 0 then
      ⟨0,![none,none,some (bits 1)],fun _=>.right⟩ else
      ⟨1,fun _=>none,![.left,.stay,.stay]⟩)
    else if q.val=1 then some (if bits 0 then
      ⟨1,fun _=>none,![.left,.stay,.stay]⟩ else
      ⟨2,fun _=>none,![.right,.stay,.stay]⟩) else none

end Theorem25Completion.WalkRawSegment
