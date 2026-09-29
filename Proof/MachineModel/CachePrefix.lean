import Proof.MachineModel.CacheStart

/-! The physical total finalizer feeds exactly one native cache header.
The original total template and incidence scratch stay outside the header bank. -/
namespace NearCubicWires.ExtDecompositionBatch.CachePrefix
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 19) : Fin 21:=i.natAdd 2
noncomputable def headerMachine:=RecoveryFocus.machine slots CacheHeader.machine
noncomputable def machine:=Composition.machine CacheStart.machine headerMachine

end NearCubicWires.ExtDecompositionBatch.CachePrefix
