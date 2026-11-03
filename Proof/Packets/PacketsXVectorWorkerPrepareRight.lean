import Proof.Packets.PacketsXVectorWorkerPrepareLevel

/-! A level provider may physically clear the old right operand. This join
tracks its actual returned right packet while preserving the left packet,
vector banks, and controller scratch layout. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section
attribute [local irreducible] VectorWorkerArena.windowMachine VectorWorkerArena.deltaTag prepareLevel

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
