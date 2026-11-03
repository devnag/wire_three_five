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
import Proof.Packets.PacketsXLiteralAlphabet
import Proof.Packets.PacketsXNormalizedRing
import Proof.Packets.PacketsXSubstitutionNatInvariant
import Proof.Packets.PhysicalIndexedAt
import Proof.Packets.PhysicalRepeatStep

/-! The actual child loop, with ordered literal-polynomial accumulator and
existential private workspace. Its provider parameter is the concrete delta
machine from VectorBottomUpMachine; the provider run is discharged separately
by the metadata, window emission, and normalization assembly. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NormalizedFiniteTransport
noncomputable section

attribute [local irreducible] VectorWorkerArena.reusableMetadata VectorChildTransaction.machine
attribute [local irreducible] delta child children childBody

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
