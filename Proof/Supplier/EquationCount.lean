import Proof.Supplier.EquationCountReady

/-! The original framed equation-row input supplies the complete physical
count/capacity bank. Its raw cut cursor and external source are retained. -/
namespace NearCubicWires.RepairOrdinary.EquationCountCold
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (j : Fin 32) : Fin 62 :=
  if j.val=0 then 12 else if j.val=1 then 22 else if j.val=2 then 32
  else if j.val=3 then 33 else ⟨j.val+30,by omega⟩
noncomputable def first := TapeEmbedding.machine 28 EquationHeaderBoot.machine
noncomputable def last := RecoveryFocus.machine slots EquationCountReady.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.EquationCountCold
