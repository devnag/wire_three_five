import Proof.Supplier.RowTupleDerivedEnumeration

/-! The actual cold binary enumerator pays one recorded return of its
produced tuple stream. Its recording tape starts blank and its exponential
candidate count is never supplied as a runtime unary driver. -/
namespace NearCubicWires.RepairOrdinary.RowTupleEnumerationReady
open LocalBitMultitape RecoveryExecution
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def selected (i : Fin 40) : Bool := decide (i=17)
noncomputable def machine := MaskedReset.machine RowTupleDerivedEnumeration.machine selected

end NearCubicWires.RepairOrdinary.RowTupleEnumerationReady
