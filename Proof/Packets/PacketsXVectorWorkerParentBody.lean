import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.NormalizedAdditionData
import Proof.Packets.NormalizedMultiplyData
import Proof.Packets.NormalizerCold
import Proof.Packets.PacketVector
import Proof.Packets.PacketsXNormalizedFiniteTransport
import Proof.Packets.PacketsXNormalizerOperations
import Proof.Packets.ReusableArithmeticLeft
import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.VectorAccumulatorRight
import Proof.Packets.VectorChildTransaction

/-! Full parent body: paid counter reset, actual child execution, indexed
parent write, and accumulator erasure. The counted child run is a composable
Step from child_loop_run, with no extra tape or scalar oracle. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section


attribute [local irreducible] resetChild children commit parentBody

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
