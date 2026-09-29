import Proof.Supplier.RowMaskIndexAppend

/-! Physical monomial-mask workspace: source cursor, occurrence-index
template, live occurrence word, and live occurrence-count sentinel. -/
namespace NearCubicWires.RepairOrdinary.RowMaskBodyParts
open LocalBitMultitape RecoveryExecution Streaming RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def appendSlots : Fin 2→Fin 4 := ![1,2]
noncomputable def appendMachine := RecoveryFocus.machine appendSlots RowMaskIndexAppend.machine

def indexSlots : Fin 1→Fin 4 := fun _=>1
noncomputable def indexMachine := RecoveryFocus.machine indexSlots RowCoordinateIncrement.machine

def moveMachine : Machine 4 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q bits=>if q.val=0 then some ⟨1,
    ![none,none,none,if bits 0 then some true else none],
    ![.right,.stay,.stay,if bits 0 then .right else .stay]⟩ else none

noncomputable def tailMachine := Composition.machine indexMachine moveMachine

end NearCubicWires.RepairOrdinary.RowMaskBodyParts
