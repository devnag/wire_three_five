import Proof.Packets.PacketsXVectorWorkerTransfer
import Proof.Packets.NormalizedAdditionData
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizerCold
import Proof.Packets.PacketVector
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.ReusableArithmeticLeft
import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.VectorAccumulatorRight
import Proof.Packets.VectorChildTransaction
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.PhysicalIndexedAt
import Proof.Packets.PhysicalRepeatStep

/-! Full299-tape descending level execution with an exact resident vector
invariant. Level bodies are the concrete preparation, parent loop, and paid
bank-turnover program; the only abstract parameters are finite provider
machines whose actual run lemmas instantiate the compositional premise. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

attribute [local irreducible] levelBody machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
