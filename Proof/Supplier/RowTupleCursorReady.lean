import Proof.Supplier.RowTupleMaskLoop

/-! One tuple in the actual selected stream advances its retained input
cursor and returns the occurrence stream/count to their consumer heads.
The complete final store is exposed for the enclosing equation/list loop. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorReady
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 13) : Bool := decide (i=2)
noncomputable def first := MaskedReset.machine RowTupleMaskLoop.machine selected
def slots : Fin 1→Fin 14 := fun _=>3
noncomputable def last := RecoveryFocus.machine slots UnaryTemplate.machine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowTupleCursorReady
