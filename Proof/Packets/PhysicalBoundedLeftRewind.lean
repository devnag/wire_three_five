import Proof.Amplification.RecoveryTimedExecution
import Proof.MachineModel.OrdinaryUnaryTemplate

/-! A paid unary capacity bounds the current cursor. The fixed machine walks
that many cells left, with the physical head's usual clamp at zero, then
restores its capacity driver. It never changes either tape. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace Completion.PhysicalBoundedLeftRewind
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def machine : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==2
  rule:=fun s bs=>if s.val=0 then some
    (if bs 0 then ⟨0,fun _=>none,![.right,.left]⟩
      else ⟨1,fun _=>none,![.left,.stay]⟩)
    else if s.val=1 then some
      (if bs 0 then ⟨1,fun _=>none,![.left,.stay]⟩
        else ⟨2,fun _=>none,![.right,.stay]⟩) else none

end Completion.PhysicalBoundedLeftRewind
