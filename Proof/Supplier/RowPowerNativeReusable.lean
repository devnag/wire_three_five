import Proof.Supplier.RowPowerNativeReset

/-! A native signed field with physically reusable scratch. The source and
two append cursors survive; the capacity driver pays for every erased cell. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReusable
open LocalBitMultitape RecoveryExecution RecoveryRootRound RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 9 → Fin 15 := ![1,2,3,4,5,6,7,8,12]
def eraseSlots : Fin 11 → Fin 15 :=
  Fin.addCases (m := 10) (n := 1) (motive := fun _ => Fin 15)
    (Fin.addCases (m := 9) (n := 1) (motive := fun _ => Fin 15)
      workSlots (fun _ : Fin 1 => 13)) (fun _ : Fin 1 => 14)
noncomputable def first := TapeEmbedding.machine 2 RowPowerNativeReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 9)
noncomputable def machine := Composition.machine first last


end NearCubicWires.RepairOrdinary.RowPowerNativeReusable
