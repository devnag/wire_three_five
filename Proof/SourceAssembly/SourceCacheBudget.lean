import Proof.SourceAssembly.SourceCacheBound
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourceCacheBudget
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairRepresentation P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ6fbdd6f776f6447d_Source

theorem occurrence_eq (B q w : Nat) :
    PoolEntryOccurrence.budget B q w=409600*(B+q+w+1)^2+4*B+22 := by
  unfold PoolEntryOccurrence.budget PoolEntryBaseline.budget PoolEntry.uniformBudget PoolEntry.reserve
  ring

theorem loop_eq (N B q w : Nat) :
    PoolEntryLoop.budget N B q w=N*(409600*(B+q+w+1)^2+4*B+25)+3 := by
  simp only [PoolEntryLoop.budget,occurrence_eq]

theorem cache_eq {q : Nat} (a : DecompositionAlgorithm)
    (occ : List (SupportedNormalizedGate q)) (B w P : Nat) :
    PCJ6e421fabe2aa4155_SourceCache.budget a occ B w P=
      occ.length*(409600*(B+q+w+1)^2+4*B+25)+
      Cold.runtimeCoefficient a*(P+2)^Cold.runtimeDegree a+6 := by
  simp only [PCJ6e421fabe2aa4155_SourceCache.budget,loop_eq]
  ring

end PCJ6e421fabe2aa4155_SourceCacheBudget
