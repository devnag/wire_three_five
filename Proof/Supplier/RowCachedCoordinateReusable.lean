import Proof.Supplier.RowCachedCoordinateReset

/-! Complete reusable selected-child coordinate call. Both scratch banks are
physically cleared, the original cache returns to head0, and each P/N cursor
stays at the newly appended delimiter. The two capacity tapes are real inputs. -/
namespace NearCubicWires.RepairOrdinary.RowCachedCoordinateReusable
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 5 → Fin 23 := ![16,17,20,21,22]
noncomputable def first := TapeEmbedding.machine 2 RowCachedCoordinateReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowCachedCoordinateReusable
