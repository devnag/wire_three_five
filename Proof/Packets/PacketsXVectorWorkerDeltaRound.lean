import Proof.Packets.PacketVector
import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.PacketsXVectorWorkerArena
import Proof.Packets.PacketsXVectorWorkerCleanup
import Proof.Packets.PacketsXVectorWorkerReuse
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.PacketsXVectorWorkerBranch

/-! One actual delta call: overwrite the scalar frames, inspect the two
physical validity bits, run the finite literal-window provider when valid,
and erase all numeric scratch before the next child. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

attribute [local irreducible] VectorWorkerArena.reusableMetadata VectorWorkerArena.erase
attribute [local irreducible] VectorWorkerArena.deltaBranch delta

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
