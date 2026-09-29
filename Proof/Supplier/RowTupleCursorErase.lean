import Proof.Supplier.RowTupleCommonEquation
import Proof.Supplier.RowTupleCursorReady

/-! Paid per-tuple cleanup clears only the coordinate counter, occurrence
stream and occurrence count, and restores their consumer heads. All other
tapes and live cursors are retained. -/
namespace NearCubicWires.RepairOrdinary.RowTupleCursorErase
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def eraseSlots : Fin 5→Fin 48 := ![15,23,24,33,34]
noncomputable def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 3)

def shift (forward : Bool) : Machine 48 2 where
  descriptionBits:=0
  start:=0
  halted:=fun q=>q.val==1
  rule:=fun q _=>if q.val=0 then some ⟨1,fun _=>none,
    fun i=>if i=15 ∨ i=24 then (if forward then .right else .left) else .stay⟩ else none

noncomputable def first := Composition.machine (shift false) erase
noncomputable def machine := Composition.machine first (shift true)

end NearCubicWires.RepairOrdinary.RowTupleCursorErase
