import Proof.SourceAssembly.SourcePoolAllocate
import Proof.SourceAssembly.SourcePoolBoot
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ6e421fabe2aa4155_SourcePoolInitialize
open NearCubicWires LocalBitMultitape ExtDecompositionBatch ExtIncidence RepairOrdinary RepairRepresentation
open SourceInterfaces RecoveryRootRound P1Closure RepairSource RepairSource.VerifierDecoding
open PCJ6e421fabe2aa4155_SourcePoolBank
noncomputable section

def worker (i : Fin 132) : Fin 145:=(PCJ6e421fabe2aa4155_SourcePoolAllocate.worker i).castAdd 2
def bootSlots : Fin 134→Fin 145:=Fin.addCases (motive:=fun _=>Fin 145) worker (fun j : Fin 2=>j.natAdd 143)
theorem boot_inj : Function.Injective bootSlots:=by decide
def first:=TapeEmbedding.machine 2 PCJ6e421fabe2aa4155_SourcePoolAllocate.machine
def boot:=RecoveryFocus.machine bootSlots PCJ6e421fabe2aa4155_SourcePoolBoot.machine
def machine:=Composition.machine first boot
def input {q : Nat} (live : Finset (Fin q)) (B N : Nat) (source : List Bool) : Fin 145→List Bool:=
  Fin.addCases (motive:=fun _=>List Bool)
    (NativeFanout.input (m:=132) (data live B N source) (PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q))
    (fun _ : Fin 2=>[])
def budget (B q N : Nat):=(2*PCJ6e421fabe2aa4155_SourcePoolCapacity.value B q+4)+1+(2*natBitLength (2*N)+5)
def head (N : Nat) (i : Fin 132):=if i=61 then (prefixWord N).length else if i=131 then 1 else 0


end
end PCJ6e421fabe2aa4155_SourcePoolInitialize
