import Proof.Packets.PacketsXVectorPhaseDouble
import Proof.Packets.PacketsXVectorPhaseWidth

/-! Closed terminal-to-delta metadata phase change. Only the literal count
and its logarithmic subset width change; all working tapes are returned. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def phaseChange := Composition.machine phaseDouble regenerateWidth

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorNumericArena
