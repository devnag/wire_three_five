import Proof.Supplier.RowCommonReusable

/-! A single explicit allocation pays the common-width coefficient and its
complete physical cleanup. The remaining cold caller must produce these
raw counters; no local capacity inequality survives this endpoint. -/
namespace NearCubicWires.RepairOrdinary.RowCommonBounds
open LocalBitMultitape RepairRepresentation RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def capacity {n : ℕ} (gs : List (ExactThresholdGate n)) (m p : ℕ) :=
  16384*(m+1)*RowCachedCoordinateBounds.size gs (RowCachedCoordinateBounds.width gs)+16*p+64

end NearCubicWires.RepairOrdinary.RowCommonBounds
