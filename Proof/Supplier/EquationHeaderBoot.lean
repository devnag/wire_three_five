import Proof.Supplier.EquationHeaderRead

/-! Read the physical odd-coordinate flag and reset the three parsed count
drivers. The entry remains the original framed row word and blank scratch. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderBoot
open LocalBitMultitape RecoveryExecution
open RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def boot : Machine 34 2 where
  descriptionBits := 0
  start := 0
  halted := fun q => q.val==1
  rule := fun _ bs => some ⟨1,
    fun i => if i=33 then some (bs 1) else none,
    fun i => if i=1 then .right else if i=12 ∨ i=22 ∨ i=32 then .left else .stay⟩


noncomputable def first := TapeEmbedding.machine 1 EquationHeaderRead.machine
noncomputable def machine := Composition.machine first boot

end NearCubicWires.RepairOrdinary.EquationHeaderBoot
