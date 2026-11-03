import Proof.Supplier.RowTupleMaskLoop
import Proof.Supplier.RowMaskLookupReusable
import Proof.Supplier.RowMaskMeaning

/-! The tuple's actual occurrence stream is returned to its first cell and
its counted driver to head1, ready for the common-width equation consumer. -/
namespace NearCubicWires.RepairOrdinary.RowTupleMaskReady
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

end NearCubicWires.RepairOrdinary.RowTupleMaskReady
