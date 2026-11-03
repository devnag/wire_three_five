import Proof.Rows.MaskSeek

/-! Counted backwards cursor return. The source word and its runtime width
and row-count drivers are preserved; no movement log is needed. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskBack
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.VerifierDecoding

def body : Machine 3 3 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==2
  rule := fun q scan=>
    if q.val=0 then some (if scan 0 then ⟨0,fun _=>none,![.right,.left,.stay]⟩
      else ⟨1,fun _=>none,![.left,.stay,.stay]⟩)
    else if q.val=1 then some (if scan 0 then ⟨1,fun _=>none,![.left,.stay,.stay]⟩
      else ⟨2,fun _=>none,![.right,.stay,.stay]⟩)
    else none

noncomputable def machine := RepeatMachine.machine body (fun _ _=>true)

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskBack
