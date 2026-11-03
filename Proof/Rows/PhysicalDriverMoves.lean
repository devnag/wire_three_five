import Proof.Amplification.RecoveryTimedExecution
import Proof.MachineModel.Runs

/-! Single paid head moves, retaining all tape words. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warningAsError true
namespace Completion.PhysicalDriverMoves
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def machine (t : Nat) (move : HeadMove) : Machine t 2 where
  descriptionBits:=0
  start:=0
  halted:=fun s=>s.val==1
  rule:=fun s _=>if s.val=0 then some ⟨1,fun _=>none,fun _=>move⟩ else none

end Completion.PhysicalDriverMoves
