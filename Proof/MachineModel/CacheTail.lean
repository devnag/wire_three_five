import Proof.MachineModel.CacheRewind

/-! One paid body rewind, one Records call for the whole ordered child family,
and one paid cache rewind. No second occurrence loop is used. -/
namespace NearCubicWires.ExtDecompositionBatch.CacheTail
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound RepairOrdinary.DecompositionSource
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bodySlots : Fin 3 → Fin 7:=![0,5,6]
def cacheSlots : Fin 3 → Fin 7:=![2,5,6]
noncomputable def bodyMachine:=RecoveryFocus.machine bodySlots CompetitorRecordRewind.machine
noncomputable def cacheMachine:=RecoveryFocus.machine cacheSlots CompetitorRecordRewind.machine
noncomputable def recordsMachine:=TapeEmbedding.machine 2 Records.machine
noncomputable def machine:=Composition.machine (Composition.machine bodyMachine recordsMachine) cacheMachine


end NearCubicWires.ExtDecompositionBatch.CacheTail
