import Proof.Packets.PhysicalSupportReturn
import Proof.PCP.VerifierDecodingRepeatBody

/-! A physical fixed-width record reversal. The width and record-count
sentinels are retained; each source row is copied in its original bit order. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def body : Machine 3 5 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val == 4
  rule := fun q scan =>
    if q.val = 0 then
      some (if scan 0 then ⟨0, fun _ => none, ![.right,.left,.stay]⟩
        else ⟨1, fun _ => none, ![.left,.stay,.stay]⟩)
    else if q.val = 1 then
      some (if scan 0 then ⟨1, ![none,none,some (scan 1)], ![.left,.right,.right]⟩
        else ⟨2, fun _ => none, ![.right,.stay,.stay]⟩)
    else if q.val = 2 then
      some (if scan 0 then ⟨2, fun _ => none, ![.right,.left,.stay]⟩
        else ⟨3, fun _ => none, ![.left,.stay,.stay]⟩)
    else if q.val = 3 then
      some (if scan 0 then ⟨3, fun _ => none, ![.left,.stay,.stay]⟩
        else ⟨4, fun _ => none, ![.right,.stay,.stay]⟩)
    else none

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskReverse
