import Proof.SourceAssembly.SourcePoolBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolAllocate
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open PCJ6e421fabe2aa4155_SourcePoolBank
noncomputable section

def worker (i : Fin 132) : Fin 143:=((i.castAdd 1).natAdd 9).castAdd 1
def machine:=NativeFanout.machine select

end
end PCJ6e421fabe2aa4155_SourcePoolAllocate
