import Proof.Supplier.RowTupleSubsets

/-! One tuple digit is read at the live source cursor. Reusable comparisons
and an overwriting copy retain the short binary fields between digits. -/
namespace NearCubicWires.RepairOrdinary.RowTupleFilterParts
open LocalBitMultitape RecoveryExecution RecoveryRootRound SignedSortKey
open RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def readMachine := TapeEmbedding.machine 9 FieldMachine.machine

def compareSlots (prior : Bool) : Fin 4→Fin 12 :=
  if prior then ![1,6,7,5] else ![1,3,4,5]
noncomputable def compareMachine (prior : Bool) :=
  RecoveryFocus.machine (compareSlots prior) RecoveryPrefixCompare.machine

def updateMachine : Machine 12 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some ⟨1,
    fun i=>if i=8 then some true else if i=9 then some (bits 9 && ((!bits 8) || (!bits 7)) && bits 4)
      else none,fun _=>.stay⟩ else none

def copySlots : Fin 4→Fin 12 := ![1,6,10,11]
noncomputable def copyMachine := RecoveryFocus.machine copySlots MatrixFrameCopy.machine

end NearCubicWires.RepairOrdinary.RowTupleFilterParts
