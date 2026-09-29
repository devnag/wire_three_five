import Proof.Supplier.RowTupleFilterParts

/-! The executed digit body reads, checks the bound and strict ordering,
updates its accumulated validity flag, and saves the current digit. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterBody
open LocalBitMultitape RecoveryExecution RowTupleFilterParts SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

noncomputable def bounded := Composition.machine readMachine (compareMachine false)
noncomputable def ordered := Composition.machine bounded (compareMachine true)
noncomputable def guarded := Composition.machine ordered updateMachine
noncomputable def machine := Composition.machine guarded copyMachine

end NearCubicWires.RepairOrdinary.RowTupleFilterBody
