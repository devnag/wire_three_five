import Proof.SourceAssembly.SourceCacheReady

/- Actual cache-program support bounds, independent of retained zero reserve.
The bound excludes allocation and prior clearing; it is a maximum with the old
backing, so reuse does not create a reserve recurrence. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourceCacheBound
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJc4297ab269d8423a_Source PCJ6fbdd6f776f6447d_Source
open PCJ6e421fabe2aa4155_SourceCache
noncomputable section
attribute [local irreducible] PCJ6e421fabe2aa4155_SourceCache.machine
  PCJ6e421fabe2aa4155_SourceCache.readyMachine PoolCold.machine Cold.machine

end
end PCJ6e421fabe2aa4155_SourceCacheBound
