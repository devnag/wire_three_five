import Proof.Amplification.RecoveryTimedExecution
import Proof.Foundations.OrdinaryStreaming
import Proof.MachineModel.Runs

/-! Decode the payload of one actual framed coordinate into raw seed bits. -/
namespace Theorem25Completion.WalkUnframe
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 2
  rule := fun q bits => if q.val=0 then some
      ⟨if bits 0 then 1 else 2,![none,none],![.right,.stay]⟩
    else if q.val=1 then some ⟨0,![none,some (bits 0)],fun _ => .right⟩ else none

end Theorem25Completion.WalkUnframe
