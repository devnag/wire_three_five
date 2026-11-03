import Proof.Packets.PacketsXWalkLiteralAdvance
import Proof.Packets.PacketVector
import Proof.Packets.PhysicalRepeatStep

/-! Concrete counted-walk state: original vertex and seed, resident bounded
workspace, exact ordered transcript prefix, and remaining allocated zeros. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralLoop
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open NearCubicWires.SupplierWalk NearCubicWires.CanonicalFourfoldRowProgram NearCubicWires.RepairSource.CloseoutRawRows
open PCJ9eff70d512234a4c_Fixed.Materializer
open CloseoutRowsModeCache NormalizedFiniteTransport Theorem25Completion.CycleBounds
open VectorBottomUp SubstitutionCensus
noncomputable section

variable {population active depth n : Nat}

def body := Composition.machine WalkLiteralVisit.machine WalkLiteralAdvance.machine

end
end Theorem25Completion.WalkLiteralLoop
