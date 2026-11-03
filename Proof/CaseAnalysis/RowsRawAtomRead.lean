import Proof.CaseAnalysis.RowsRawAtomSeek

/-! One original variable block selects and appends its actual cached
polynomial. The index is consumed; only logical cache bytes are scanned.
The existing row copier and marker writer are used without reparsing. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRead
open LocalBitMultitape RecoveryExecution ExtDecompositionBatch
open CloseoutRowsRawPolynomialAdd
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def seekSlots : Fin 2→Fin 5:=![0,1]
noncomputable def seek:=RecoveryFocus.machine seekSlots CloseoutRowsRawAtomSeek.machine
noncomputable def machine:=Composition.machine (Composition.machine seek rightMachine) finish

end NearCubicWires.RepairOrdinary.CloseoutRowsRawAtomRead
