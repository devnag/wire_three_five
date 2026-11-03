import Proof.Packets.PhysicalParityRestore

/-! Physical conditional decoding of one framed support record. The decision
is read from the coefficient tape; each retained row increments a real unary
counter, while a rejected row emits no mask bits. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.MaskSelect
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.RepairSource.VerifierDecoding

@[simp] theorem read_flag (b : Bool) : readTapeBit [b] 0 = b := rfl

def machine : Machine 4 6 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==5
  rule := fun q scan =>
    if q.val=0 then
      some ⟨if scan 0 then 1 else 2,fun _ => none,![.right,.stay,.stay,.stay]⟩
    else if q.val=1 then
      some ⟨0,![none,if scan 3 then some (scan 0) else none,none,none],
        ![.right,if scan 3 then .right else .stay,.stay,.stay]⟩
    else if q.val=2 then some ⟨3,fun _ => none,![.right,.stay,.stay,.stay]⟩
    else if q.val=3 then some ⟨4,fun _ => none,![.right,.stay,.stay,.stay]⟩
    else if q.val=4 then
      some ⟨5,![none,none,if scan 3 then some true else none,none],
        ![.stay,.stay,if scan 3 then .right else .stay,.stay]⟩
    else none

end PCJ9eff70d512234a4c_Fixed.Materializer.MaskSelect
