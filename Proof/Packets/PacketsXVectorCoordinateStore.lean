import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.PacketVector

/-! Physically replace the next-bank coordinate at the live candidate index
with the completed right operand. Every arithmetic operand is retained. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def coordinateStoreSlots : Fin 6→Fin 296:=![31,257,26,27,258,263]
attribute [local irreducible] PacketBank.storeSelectedZero
def coordinateStore:=RecoveryFocus.machine coordinateStoreSlots PacketBank.storeSelectedZero

attribute [local irreducible] coordinateStore

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
