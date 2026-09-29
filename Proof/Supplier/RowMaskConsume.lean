import Proof.Supplier.RowMaskPositionParts

/-! Consume the selected raw incidence row in the retained nine-tape bank.
The same machine accepts the allocated zero-padded index template. -/
namespace NearCubicWires.RepairOrdinary.RowMaskConsume
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 5→Fin 9 := ![0,1,2,3,4]
noncomputable def machine := RecoveryFocus.machine slots RowMaskLoop.machine

end NearCubicWires.RepairOrdinary.RowMaskConsume
