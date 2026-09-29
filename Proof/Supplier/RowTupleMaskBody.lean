import Proof.Supplier.RowMaskLookupReusable
import Proof.Supplier.RowTupleDerivedEnumeration

/-! Each tuple digit is read into the actual mask-lookup bound tape. The
lookup then appends that cached monomial's occurrence positions and updates
the physical count, retaining repeated occurrences across selected rows. -/
namespace NearCubicWires.RepairOrdinary.RowTupleMaskBody
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding RowMaskPositionParts
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readSlots : Fin 3→Fin 12 := ![10,6,11]
noncomputable def read := RecoveryFocus.machine readSlots FieldMachine.machine
noncomputable def lookup := TapeEmbedding.machine 2 RowMaskLookupReusable.machine
noncomputable def machine := Composition.machine read lookup

end NearCubicWires.RepairOrdinary.RowTupleMaskBody
