import Proof.Amplification.RecoveryPaddedCopyMeaning
import Proof.Supplier.EquationWidenLoop
import Proof.Supplier.RowCoordinateIncrement

/-! Append the physically widened field to the live cut stream. The source,
width and copy workspace retain their heads; only the output cursor moves. -/
namespace NearCubicWires.RepairOrdinary.RowFieldPaddingAppend
open LocalBitMultitape RecoveryExecution RecoveryRootRound MatrixScoreBatch
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def padSlots : Fin 4→Fin 5 := fun i=>i.castAdd 1
def copySlots : Fin 3→Fin 5 := ![1,4,3]
noncomputable def first := RecoveryFocus.machine padSlots RecoveryColdPaddedCopy.machine
noncomputable def last := RecoveryFocus.machine copySlots PCPSerializerReuse.copyMachine
noncomputable def machine := Composition.machine first last

end NearCubicWires.RepairOrdinary.RowFieldPaddingAppend
