import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.PacketVector
import Proof.Packets.VectorTransferReady

/-! Actual turnover of the complete next vector into the previous vector in
the full298-port level arena, retaining all numeric workspace and drivers. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section


attribute [local irreducible] VectorTransfer.machine transfer

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
