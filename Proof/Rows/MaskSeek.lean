import Proof.Rows.MaskReverseLoop

/-! Paid traversal to the end of a fixed-width bank, preserving its width
and actual unary row count for the subsequent reversing copy. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskSeek
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def body : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=>
    if q.val=0 then some (if scan 0 then ⟨0,fun _=>none,![.right,.right,.stay]⟩
      else ⟨1,fun _=>none,![.left,.stay,.stay]⟩)
    else if q.val=1 then some (if scan 0 then ⟨1,fun _=>none,![.left,.stay,.stay]⟩
      else ⟨2,fun _=>none,![.right,.stay,.stay]⟩)
    else none

noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskSeek
