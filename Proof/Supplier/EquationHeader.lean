import Proof.Supplier.EquationCount
import Proof.Supplier.EquationHeaders

/-! The original framed row now supplies the exact output headers as well
as every retained loop/count/capacity input. -/
namespace NearCubicWires.RepairOrdinary.EquationHeaderCold
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 52 → Fin 111 := ![42,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,44,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,50,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110]
noncomputable def first := TapeEmbedding.machine 49 EquationCountCold.machine
noncomputable def last := RecoveryFocus.machine slots EquationHeaders.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.EquationHeaderCold
