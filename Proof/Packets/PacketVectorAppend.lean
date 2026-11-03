import Proof.Packets.PacketVector
import Proof.Packets.VectorControllerLayout
import Proof.Packets.VectorTransferReady

/-! Append an entire produced coordinate vector to a resident transcript.
The source is cleared and rewound; the destination cursor advances past the
copied vector, preserving its prefix and remaining allocated suffix. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorAppend
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.VerifierDecoding
open VectorTransfer
noncomputable section

def machine := Composition.machine VectorTransfer.loop
  (Composition.machine VectorTransfer.backSource VectorTransfer.backSource)


end
end PCJ9eff70d512234a4c_Fixed.Materializer.PacketVectorAppend
