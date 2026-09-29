import Proof.MachineModel.GeneratedAmplifierCopy

/-! A verbatim framed stream copy keeps both cursors at the next field.
The Pascal row prefix uses it to copy the existing leading one while
positioning the right input at the second original entry. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsTouching.FrameStream
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def machine : Machine 2 3 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==2
  rule:=fun q bits=>if q.val=0 then
      some ⟨if bits 0 then 1 else 2,![none,some (bits 0)],fun _=>.right⟩
    else if q.val=1 then some ⟨0,![none,some (bits 0)],fun _=>.right⟩ else none

end NearCubicWires.RepairOrdinary.CloseoutRowsTouching.FrameStream
