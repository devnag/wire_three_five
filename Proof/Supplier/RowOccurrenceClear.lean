import Proof.Supplier.RowIndexField

/-! Reuse the existing row capacity driver to erase the consumed occurrence
index. Only that index and its erase log are touched; the next stream cursor
and the two growing coefficient tapes remain live. -/
namespace NearCubicWires.RepairOrdinary.RowOccurrenceClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots : Fin 3 → Fin 24 := ![19,21,22]
def advance : Machine 24 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q _=>if q.val=0 then some
    ⟨1,fun _=>none,fun i=>if i=19 then .left else .stay⟩ else none
noncomputable def erase := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1)
noncomputable def machine := Composition.machine advance erase

end NearCubicWires.RepairOrdinary.RowOccurrenceClear
