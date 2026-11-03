import Proof.Supplier.RowCommonReset

/-! Physically erase the common-width coefficient scratch, preserving the
native cache, occurrence stream, dimensions and live cut-output cursor. -/
namespace NearCubicWires.RepairOrdinary.RowCommonClear
open LocalBitMultitape RepairRepresentation RecoveryExecution RecoveryRootRound Streaming
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def workSlots : Fin 10→Fin 35 := ![10,11,16,19,25,26,27,28,30,32]
def eraseSlots : Fin 12→Fin 35 := Fin.addCases (m:=11) (n:=1) (motive:=fun _=>Fin 35)
  (Fin.addCases (m:=10) (n:=1) (motive:=fun _=>Fin 35) workSlots (fun _=>33)) (fun _=>34)
noncomputable def first := TapeEmbedding.machine 2 RowCommonReset.machine
noncomputable def last := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 10)
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowCommonClear
