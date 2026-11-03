import Proof.Packets.PacketsXVectorCoordinateStore
import Proof.Packets.PacketsXVectorWorkerLookup
import Proof.Packets.PacketsXVectorBottomUpMachine
import Proof.Packets.VectorControllerLayout
import Proof.Rows.PhysicalFocusBoundary
import Proof.Packets.PhysicalIndexedAt
import Proof.Packets.PhysicalRepeatStep

/-! Enumerate final coordinates, run the whole-coordinate callback, and store
the exact answers in ascending slots. The resulting resident bank can feed
the frozen outer fold in its required order. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section


attribute [local irreducible] lookupRight coordinateStore
def coordinateBody {s : Nat} (callback : Machine 296 s):=
  Composition.machine lookupRight (Composition.machine callback coordinateStore)
def coordinateCollect {s : Nat} (callback : Machine 296 s):=
  PhysicalIndexedAt.machine (258 : Fin 296) (coordinateBody callback)

attribute [local irreducible] coordinateBody coordinateCollect

end
end PCJ9eff70d512234a4c_Fixed.Materializer.VectorBottomUp
