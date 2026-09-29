import Proof.Supplier.RowBinaryClear

/-! Retained packed-mask positioning uses a short binary row counter and
one physical raw-row skip. The native occurrence output remains live. -/
namespace NearCubicWires.RepairOrdinary.RowMaskPositionParts
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def counterSlots : Fin 4→Fin 9 := ![5,6,7,8]
noncomputable def counterMachine := RecoveryFocus.machine counterSlots RowTupleCounter.machine

def skipSlots : Fin 3→Fin 9 := ![4,0,2]
noncomputable def skipMachine := RecoveryFocus.machine skipSlots (MatrixRawBlock.machine false)

end NearCubicWires.RepairOrdinary.RowMaskPositionParts
