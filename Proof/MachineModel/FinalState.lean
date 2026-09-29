import Proof.MachineModel.FinalLayout

/-! The occurrence loop's actual accumulated streams meet the finalizer entry.
This ties cache bytes and occurrence counts to the SAME executed constructors. -/
namespace NearCubicWires.ExtDecompositionBatch
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.DecompositionSource RepairOrdinary.RecoveryRootRound SupplierPipeline
open RepairOrdinary.CloseoutRowsCircuitBottom
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
variable (a:DecompositionAlgorithm)

def bodyWord {q:ℕ} (occ:List (SupportedNormalizedGate q)):=(GS a occ).flatMap exactWord

end NearCubicWires.ExtDecompositionBatch
