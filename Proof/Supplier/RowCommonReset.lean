import Proof.Supplier.RowCommonCoefficient

/-! Restore the dedicated occurrence cursor after the common-width append.
All scratch lengths are bounded using the executed prefix, and the physical
reset log is retained at the same paid allocation for subsequent erasure. -/
namespace NearCubicWires.RepairOrdinary.RowCommonReset
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 32) := decide (i=23)
noncomputable def machine := MaskedReset.machine RowCommonCoefficient.machine selected

end NearCubicWires.RepairOrdinary.RowCommonReset
