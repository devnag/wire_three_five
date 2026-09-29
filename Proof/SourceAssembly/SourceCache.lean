import Proof.SourceAssembly.PoolColdCompatible

/- Actual paired decomposition outputs, aliased into the binary pool consumer.
Only two supplied public words remain on the disjoint bank: the already paid
mask bitmap and the retained live-count template.  No child cache is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourceCache
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ6fbdd6f776f6447d_Source
noncomputable section

abbrev tapes (a : DecompositionAlgorithm) := 132+Cold.tapes a
def domainPort (a : DecompositionAlgorithm) : Fin (tapes a) :=
  PoolCold.slots a (Cold.port a (dom a))

def directions (a : DecompositionAlgorithm) (i : Fin (tapes a)) : HeadMove :=
  if i=domainPort a then .left else .stay

def readyMachine (a : DecompositionAlgorithm) := Composition.machine (PoolCold.machine a)
  (DecompositionCountPosition.move (directions a))

def machine (a : DecompositionAlgorithm) := TapeEmbedding.machine 373 (readyMachine a)

end
end PCJ6e421fabe2aa4155_SourceCache
