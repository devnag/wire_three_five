import Proof.Packets.PacketBankPrimitives

/-! Physical unary loop-coordinate updates. Counters have their actual false
sentinel and return to head one, so they can directly drive packet lookup. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def increment : Machine 1 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q scan=>if q.val=0 then
    some (if scan 0 then ⟨0,fun _=>none,fun _=>.right⟩
      else ⟨1,fun _=>some true,fun _=>.left⟩)
    else if q.val=1 then
      some (if scan 0 then ⟨1,fun _=>none,fun _=>.left⟩
        else ⟨2,fun _=>none,fun _=>.right⟩)
    else none

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
