import Proof.Packets.VectorCounter

/-! Paid descending unary indices for reversed level and mask traversals.
The erased last true bit remains part of the reusable physical allocation. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

def decrement : Machine 1 4 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==3
  rule:=fun q scan=>if q.val=0 then
    some (if scan 0 then ⟨0,fun _=>none,fun _=>.right⟩
      else ⟨1,fun _=>none,fun _=>.left⟩)
    else if q.val=1 then some ⟨2,fun _=>some false,fun _=>.left⟩
    else if q.val=2 then
      some (if scan 0 then ⟨2,fun _=>none,fun _=>.left⟩
        else ⟨3,fun _=>none,fun _=>.right⟩)
    else none

end PCJ9eff70d512234a4c_Fixed.Materializer.VectorCounter
