import Proof.MachineModel.CacheHeader

/-! Finalize the actual accumulated total and copy it for the one cache header.
The count template and incidence scratch are retained for their consumers. -/
namespace NearCubicWires.ExtDecompositionBatch.CacheStart
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def totalSlots : Fin 2 → Fin 21:=![0,1]
def unarySlots : Fin 3 → Fin 21:=![0,2,3]
noncomputable def totalMachine:=RecoveryFocus.machine totalSlots FinalizeT.machine
noncomputable def unaryMachine:=RecoveryFocus.machine unarySlots FinalUnary.machine
noncomputable def machine:=Composition.machine totalMachine unaryMachine

end NearCubicWires.ExtDecompositionBatch.CacheStart
