import Proof.Supplier.RowTupleEnumerationReady
import Proof.Supplier.RowTupleFramedBody

/-! The actual binary producer, paid output rewind, and complete selected
list consumer share one tuple tape. No tuple bytes or unary tuple count
are supplied at input. Native cache and common metadata remain retained. -/
namespace NearCubicWires.RepairOrdinary.RowTupleEnumeratedEquations
open LocalBitMultitape RepairRepresentation RecoveryExecution
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


def extra (w k M : ℕ) : Fin 40→List Bool := fun i=>
  if i=2 then CompareMachine.word w else if i=3 then frame (SignedSortKey.binary w (M-1))
    else if i=12 then CompareMachine.word k else if i=17 then List.replicate w true else []


end NearCubicWires.RepairOrdinary.RowTupleEnumeratedEquations
