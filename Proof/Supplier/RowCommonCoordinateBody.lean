import Proof.Supplier.RowCommonBounds

/-! The actual common-width row consumer: append one coefficient at the
shared cut width, restore its bank, and advance the coordinate on tape15. -/
namespace NearCubicWires.RepairOrdinary.RowCommonCoordinateBody
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 1→Fin 35 := fun _=>15
noncomputable def increment := RecoveryFocus.machine slots RowCoordinateIncrement.machine
noncomputable def machine := Composition.machine RowCommonClear.machine increment

end NearCubicWires.RepairOrdinary.RowCommonCoordinateBody
