import Proof.Supplier.RowTupleEnumeratedEquations

/-! Append the cached binLift signed coefficient after the complete equation.
The common row log resets only the coefficient source; append cursor stays live. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCutAppend
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 49 := ![48,31,34]
noncomputable def machine := RecoveryFocus.machine slots PCPSerializerReuse.copyMachine

end NearCubicWires.RepairOrdinary.RowTupleCutAppend
