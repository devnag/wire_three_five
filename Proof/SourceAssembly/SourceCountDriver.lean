import Proof.SourceAssembly.SourceNativeList

/- The actual decomposition loop already manufactures and retains the count
needed by the exact native-field copy. Expose it from the same executed code. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourceCountDriver
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open P1Closure SupplierPipeline SupplierEstimator RepairSource RepairSource.CloseoutFinal
noncomputable section
attribute [local irreducible] Cold.machine Cold.entryMachine Cold.batch batchMachine Prelude.occurrences FinalLayout.machine

def port (a : DecompositionAlgorithm) := Cold.old a (Prelude.driverSlot a)

end
end PCJ6e421fabe2aa4155_SourceCountDriver
