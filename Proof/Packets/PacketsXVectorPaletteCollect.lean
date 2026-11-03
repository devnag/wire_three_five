import Proof.Packets.PacketVectorAppend
import Proof.Packets.PacketsXVectorLiteralPaletteBoot

/-! The physical coordinate-bank collector shares the literal-vector
workspace. Its only outside tape is the ordered time transcript. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence
noncomputable section

def collectSlots : Fin 6 → Fin 317 := ![46,272,316,278,276,312]
def collectMachine := RecoveryFocus.machine collectSlots PacketVectorAppend.machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
