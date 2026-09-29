import Proof.SourceAssembly.SourcePoolCount
import Proof.SourceAssembly.SourceIndexExact

/- Concrete physical join: paid pool/decomposition, bounded rewind using its
retained capacity driver, exact native index frame in six new reusable ports. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourcePoolIndex
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ6fbdd6f776f6447d_Source
noncomputable section
attribute [local irreducible] PoolCold.machine Cold.machine PCJ6e421fabe2aa4155_SourceIndexExact.framed

def coldPorts (a : DecompositionAlgorithm) : Fin 5→Fin (Cold.tapes a) :=
  ![Cold.port a (str a),Cold.port a (cnt a),PCJ6e421fabe2aa4155_SourceCountDriver.port a,
    Cold.port a (drv a),Cold.port a (wsp a)]

abbrev baseTapes (a : DecompositionAlgorithm) := 132+Cold.tapes a
def old (a : DecompositionAlgorithm) (i : Fin 5) : Fin (baseTapes a) :=
  PoolCold.slots a (coldPorts a i)

def slots (a : DecompositionAlgorithm) : Fin 11→Fin (baseTapes a+6) :=
  fun i=>Fin.addCases (m:=5) (n:=6) (motive:=fun _=>Fin (baseTapes a+6))
    (fun i : Fin 5=>(old a i).castAdd 6) (fun i : Fin 6=>i.natAdd (baseTapes a)) i

def resetPorts (a : DecompositionAlgorithm) (i : Fin 5) := slots a (i.castAdd 6)
def indexMap : Fin 9→Fin 11 := ![0,5,6,1,2,7,8,9,10]
def indexPorts (a : DecompositionAlgorithm) (i : Fin 9) := slots a (indexMap i)

def reset (a : DecompositionAlgorithm) := RecoveryFocus.machine (resetPorts a)
  (PCJ6e421fabe2aa4155_SourceClear.rewind 3)
def frameIndex (a : DecompositionAlgorithm) := RecoveryFocus.machine (indexPorts a)
  PCJ6e421fabe2aa4155_SourceIndexExact.framed
def first (a : DecompositionAlgorithm) := TapeEmbedding.machine 6 (PoolCold.machine a)
def machine (a : DecompositionAlgorithm) := Composition.machine (Composition.machine (first a) (reset a)) (frameIndex a)

end
end PCJ6e421fabe2aa4155_SourcePoolIndex
