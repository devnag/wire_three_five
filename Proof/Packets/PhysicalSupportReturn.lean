import Proof.Amplification.RecoveryTimedExecution
import Proof.Foundations.OrdinaryComposition
import Proof.MachineModel.OrdinaryUnaryTemplate

/-! The support union consumer returns its mask and width sentinel together.
No fresh log or reset-capacity input is needed between rows; only these two
local heads move, preserving the global left/output cursors. -/
namespace NearCubicWires.RepairOrdinary.PhysicalSupportReturn
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def cfg {s : ℕ} (q : Fin s) (count dh mh : ℕ) (mask source : List Bool) (pos : ℕ) (out : List Bool) : Configuration 4 s :=
  ⟨q,![dh,mh,pos,out.length],![UnaryTemplate.tape count,mask,source,out]⟩
def machine : Machine 4 3 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==2
  rule := fun q scan => if q.val=0 then some ⟨1,fun _ => none,![.left,.stay,.stay,.stay]⟩
    else if q.val=1 then some (if scan 0 then ⟨1,fun _ => none,![.left,.left,.stay,.stay]⟩
      else ⟨2,fun _ => none,![.right,.stay,.stay,.stay]⟩) else none

end NearCubicWires.RepairOrdinary.PhysicalSupportReturn
