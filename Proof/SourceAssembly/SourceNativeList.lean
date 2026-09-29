import Proof.SourceAssembly.SourceCacheBound

/- Exact counted native-field copy. Stops after the actual number of fields,
retaining the exact logical endpoint needed by the outer ordinary framer. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ6e421fabe2aa4155_SourceNativeList
open NearCubicWires LocalBitMultitape ExtDecompositionBatch
open RepairOrdinary RepairOrdinary.RecoveryExecution RepairOrdinary.RecoveryRootRound RepairRepresentation
open RepairSource.VerifierDecoding
open PCPPQueryField (saved store nat_run payload selected)
noncomputable section

def machine := RepeatMachine.machine (PCPPQueryField.machine true) (fun _ _=>true)

end
end PCJ6e421fabe2aa4155_SourceNativeList
