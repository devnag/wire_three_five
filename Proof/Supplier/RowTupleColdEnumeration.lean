import Proof.Supplier.RowTupleFields

/-! Cold tuple enumeration from actual width, degree and bound metadata.
The program manufactures its binary zero fields, flags and scratch, then
executes the whole binary loop and returns the selected-occurrence stream. -/
namespace NearCubicWires.RepairOrdinary.RowTupleColdEnumeration
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RowTupleEnumeration
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 18) : Fin 29 := i.castAdd 11
noncomputable def enumeration := RecoveryFocus.machine slots RowTupleColdLogs.machine
noncomputable def machine := Composition.machine RowTupleColdFields.machine enumeration

end NearCubicWires.RepairOrdinary.RowTupleColdEnumeration
