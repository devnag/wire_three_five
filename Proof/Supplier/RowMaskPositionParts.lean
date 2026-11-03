import Proof.Supplier.RowBinaryClear
import Proof.MachineModel.OrdinaryMatrixRawBlock

/-! Retained packed-mask positioning uses a short binary row counter and
one physical raw-row skip. The native occurrence output remains live. -/
namespace NearCubicWires.RepairOrdinary.RowMaskPositionParts
open LocalBitMultitape RecoveryExecution RecoveryRootRound Streaming SignedSortKey RepairSource.VerifierDecoding
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

structure Data where
  source : List Bool
  pos : ℕ
  index : ℕ
  count : ℕ
  out : List Bool
  counter : ℕ
  bound : ℕ
  flag : Bool

def heads (x : Data) : Fin 9→ℕ := ![x.pos,1,x.out.length,x.count+1,1,0,0,0,0]
def counterSlots : Fin 4→Fin 9 := ![5,6,7,8]
noncomputable def counterMachine := RecoveryFocus.machine counterSlots RowTupleCounter.machine

def skipSlots : Fin 3→Fin 9 := ![4,0,2]
noncomputable def skipMachine := RecoveryFocus.machine skipSlots (MatrixRawBlock.machine false)

end NearCubicWires.RepairOrdinary.RowMaskPositionParts
