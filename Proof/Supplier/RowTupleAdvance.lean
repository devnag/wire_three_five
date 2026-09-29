import Proof.Supplier.RowTupleTerms

/-! Advance the actual tuple tape after its accepted-candidate consumer has
returned. Only the tuple and continuation flag change; the filter bank stays. -/
namespace NearCubicWires.RepairOrdinary.RowTupleAdvance
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowTupleFilterParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 4→Fin 17 := ![0,14,15,16]
noncomputable def machine := RecoveryFocus.machine slots RowTupleCounter.machine

end NearCubicWires.RepairOrdinary.RowTupleAdvance
