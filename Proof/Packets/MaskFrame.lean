import Proof.Rows.MaskProductRowReady

/-! Actual raw-mask framing with a physically incremented record counter.
The dummy tape is read-only; its cursor pays for restoring the width cursor. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution

def raw : Machine 5 5 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==4
  rule := fun q scan=>if q.val=0 then
    some ⟨if scan 0 then 1 else 2,![none,none,none,some (scan 0),none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=1 then some ⟨0,![none,none,none,some (scan 2),none],
      ![.right,.right,.right,.right,.stay]⟩
    else if q.val=2 then some ⟨3,![none,none,none,some false,none],
      ![.stay,.stay,.stay,.right,.stay]⟩
    else if q.val=3 then some ⟨4,![none,none,none,some false,some true],
      ![.stay,.stay,.stay,.right,.right]⟩
    else none

abbrev machine := Composition.machine raw MaskProduct.last

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskFrame
