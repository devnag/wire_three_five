import Proof.Packets.PacketVectorAppend

/-! Paid return across one vector of fixed-width packets. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorRewind
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open VectorTransfer PacketVectorAppend
noncomputable section

def machine := Composition.machine VectorTransfer.backTarget VectorTransfer.backTarget

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorRewind
