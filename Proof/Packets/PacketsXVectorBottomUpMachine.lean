import Proof.Packets.PacketsXVectorWorkerReuse
import Proof.Packets.PacketsXVectorWorkerBranch
import Proof.Packets.PacketsXVectorWorkerCleanup
import Proof.Packets.PacketsXVectorWorkerTag
import Proof.Packets.VectorControllerLayout

/-! The full fixed-tape bottom-up controller topology. The provider argument
is a finite machine to be instantiated by the window emitter/interpreter;
all indices, metadata arithmetic, validity branches, accumulator operations,
packet writes and double-buffer turnover are actual composed machines. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def childSlots : Fin 39→Fin 296 := fun j=>(VectorController.childSlots j).castAdd 32
def parentSlots : Fin 41→Fin 296 := fun j=>(VectorController.parentSlots j).castAdd 32
def providerSlots : Fin 256→Fin 296 := fun j=>j.castAdd 40

def child := RecoveryFocus.machine childSlots VectorChildTransaction.machine
def commit := RecoveryFocus.machine parentSlots VectorParentCommit.machine

def delta {s : Nat} (provider : Machine 256 s) :=
  Composition.machine VectorWorkerArena.reusableMetadata
    (Composition.machine
      (VectorWorkerArena.deltaBranch (RecoveryFocus.machine providerSlots provider))
      VectorWorkerArena.erase)
def childBody {s : Nat} (provider : Machine 256 s) := Composition.machine (delta provider) child

def children {s : Nat} (provider : Machine 256 s) :=
  PhysicalIndexedAt.machine (258 : Fin 296) (childBody provider)
def resetChild := PhysicalIndexReload.machine (31 : Fin 296) 0 258
def parentBody {s : Nat} (provider : Machine 256 s) :=
  Composition.machine (TapeEmbedding.machine 1 resetChild)
    (Composition.machine (children provider) (TapeEmbedding.machine 1 commit))
def parents {s : Nat} (provider : Machine 256 s) :=
  PhysicalIndexedAt.machine (259 : Fin 297) (parentBody provider)
def resetParent := PhysicalIndexReload.machine (31 : Fin 297) 0 259

def transferSlots : Fin 6→Fin 298 := ![31,257,256,0,263,297]
def transfer := RecoveryFocus.machine transferSlots VectorTransfer.machine

def prepareLevel {l : Nat} (levelProvider : Machine 256 l) :=
  Composition.machine VectorWorkerArena.windowMachine
    (Composition.machine VectorWorkerArena.deltaTag
      (RecoveryFocus.machine providerSlots levelProvider))
def levelBody {s l : Nat} (provider : Machine 256 s) (levelProvider : Machine 256 l) :=
  Composition.machine (TapeEmbedding.machine 2 (prepareLevel levelProvider))
    (Composition.machine (TapeEmbedding.machine 1 resetParent)
      (Composition.machine (parents provider) transfer))
def machine {s l : Nat} (provider : Machine 256 s) (levelProvider : Machine 256 l) :=
  PhysicalIndexedAt.downMachine (260 : Fin 298) (levelBody provider levelProvider)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
