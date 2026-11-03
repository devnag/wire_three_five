import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary

/-! Concrete per-level preparation: compute the runtime window, generate the
successor literal tag, and execute the finite ModeCache/literal/dense worker. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section


attribute [local irreducible] VectorWorkerArena.windowMachine VectorWorkerArena.deltaTag prepareLevel

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
