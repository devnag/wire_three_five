import Proof.Supplier.RowMaskConsume
import Proof.Supplier.RowMaskIndexClear

/-! Return the selected-mask bank's two short cursors to reusable zero
values by paid writes, while preserving cache, address, output, and count. -/
namespace NearCubicWires.RepairOrdinary.RowMaskBankClear
open LocalBitMultitape RecoveryExecution RecoveryRootRound RowMaskPositionParts RowMaskConsume SignedSortKey
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def indexSlots : Fin 2→Fin 9 := ![1,4]
noncomputable def indexMachine := RecoveryFocus.machine indexSlots RowMaskIndexClear.machine


def counterSlots : Fin 2→Fin 9 := ![5,8]
noncomputable def counterMachine := RecoveryFocus.machine counterSlots RowBinaryClear.machine

noncomputable def machine := Composition.machine indexMachine counterMachine

end NearCubicWires.RepairOrdinary.RowMaskBankClear
