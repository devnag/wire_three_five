import Proof.MachineModel.FinalUnary
import Proof.PCP.PCPPNativeNaturalAppend

/-! Print exactly one native total-count header from the physically produced
raw count. All private heads return, while the cache append cursor is retained. -/
namespace NearCubicWires.ExtDecompositionBatch.CacheHeader
open LocalBitMultitape RepairOrdinary RepairRepresentation ExecutableInterfaces
open RepairOrdinary.RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 18) : Bool:=decide (i≠17)
noncomputable def machine:=MaskedReset.machine PCPPNativeNaturalAppend.machine selected

end NearCubicWires.ExtDecompositionBatch.CacheHeader
