import Proof.Supplier.RowTupleFilterLoop

/-! Rewind only the tuple source after its executed digit scan. All short
fields, result flag, degree and width drivers remain in the same bank. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterReusable
open LocalBitMultitape RecoveryExecution RowTupleFilterParts RowTupleFilterBody
open RowTupleFilterMeaning SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 13) : Bool := decide (i=0)
noncomputable def machine := MaskedReset.machine RowTupleFilterLoop.machine selected

end NearCubicWires.RepairOrdinary.RowTupleFilterReusable
