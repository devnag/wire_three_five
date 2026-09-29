import Proof.Supplier.RowCoefficientEmit

/-! The whole once-per-coefficient normalizer emits the exact sign/magnitude
field consumed by the existing equation-row printer. Its two P/N source
frames and all reset cursors are retained by this seven-tape execution. -/
namespace NearCubicWires.RepairOrdinary.RowCoefficientField
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def old (i : Fin 5) : Fin 7 := i.castAdd 2
def emitSlots : Fin 4 → Fin 7 := ![2,3,5,6]
noncomputable def first := RecoveryFocus.machine old RowCoefficientNormalize.machine
noncomputable def last := RecoveryFocus.machine emitSlots RowCoefficientEmit.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowCoefficientField
