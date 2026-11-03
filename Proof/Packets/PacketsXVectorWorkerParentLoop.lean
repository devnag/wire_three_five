import Proof.Packets.PacketsXVectorWorkerChildLoop
import Proof.Packets.PacketsXVectorWorkerParentBody
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

/-! The actual parent loop fills every next-level vector slot exactly once.
Each body resets the child index, runs its full ordered child fold, stores the
result at the resident parent index, and erases the saved accumulator. -/
set_option autoImplicit false
set_option maxHeartbeats 1300000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

attribute [local irreducible] children parentBody parents

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
