import Proof.SourceAssembly.SourcePoolIndexLayout

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 2000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourcePoolIndex
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ6fbdd6f776f6447d_Source
noncomputable section
attribute [local irreducible] PoolCold.machine Cold.machine PCJ6e421fabe2aa4155_SourceIndexExact.framed
  reset frameIndex first machine
def budget {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) : Nat :=
  PoolEntryLoop.budget occ.length B q w+1+Cold.runtimeCoefficient a*(P+2)^Cold.runtimeDegree a+
    1+(2*SourceEnvelope.capacity a P+2)+1+
    (2*PCJ6e421fabe2aa4155_SourceIndexExact.budget (counts a (CloseoutRowsUniversal.pool live occ))+
      4*(natListWord (counts a (CloseoutRowsUniversal.pool live occ))).length+7)

end
end PCJ6e421fabe2aa4155_SourcePoolIndex
