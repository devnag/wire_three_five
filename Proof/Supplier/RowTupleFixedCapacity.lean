import Proof.Supplier.RowTupleCommonEquation

/-! The actual tuple-to-equation caller uses one common width and one
source-sized allocation for every tuple up to degree Q. Per-tuple width and
allocation conditions are discharged by the computed occurrence-count bound. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFixedCapacity
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound
open RepairSource.VerifierDecoding RowTupleCommonEquation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def width {n : ℕ} (gs : List (ExactThresholdGate n)) (Q : ℕ) :=
  RowCachedCoordinateBounds.width gs*(gs.length*Q)

end NearCubicWires.RepairOrdinary.RowTupleFixedCapacity
