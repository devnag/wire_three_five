import Proof.Packets.PacketsXVectorCoordinateCollect
import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary

/-! The candidate counter is physically zeroed after vector construction,
then the already resident population-plus-one driver enumerates coordinates. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] resetChild coordinateCollect

def collectedCandidates {s : Nat} (callback : Machine 296 s):=
  Composition.machine (TapeEmbedding.machine 1 resetChild) (coordinateCollect callback)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
