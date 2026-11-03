import Proof.Rows.MaskProductInner

/-! Restore the produced unary pair counter from its append cursor to the
head1 input required by ordinary counted loops. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PairCountReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def machine : Machine 1 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=>if q.val=0 then some ⟨1,fun _=>none,fun _=>.left⟩
    else if q.val=1 then some (if scan 0 then ⟨1,fun _=>none,fun _=>.left⟩
      else ⟨2,fun _=>none,fun _=>.right⟩)
    else none

end PCJ9eff70d512234a4c_Fixed.Materializer.PairCountReady
