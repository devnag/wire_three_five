import Proof.Supplier.RowPowerNativeBlock

/-! Actual local head restoration for the native-field block appender.
Cache/output cursors are excluded. Reused scratch padding is transported
through the same trace and its allocated lengths remain bounded. -/
namespace NearCubicWires.RepairOrdinary.RowPowerNativeReset
open LocalBitMultitape RecoveryExecution Streaming RepairRepresentation SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 12) := decide (1 ≤ i.val ∧ i.val < 10)
noncomputable def machine := MaskedReset.machine RowPowerNative.machine selected
def rawTime (z : ℤ) (w : ℕ) := 6*natBitLength z.natAbs+2*w+11

end NearCubicWires.RepairOrdinary.RowPowerNativeReset
