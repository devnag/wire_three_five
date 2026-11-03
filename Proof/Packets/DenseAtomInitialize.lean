import Proof.Packets.NativeIndexedAtom
import Proof.Packets.PacketVector
import Proof.Packets.PhysicalZeroBank

/-! The dense atom bank is physically allocated from the measured support
width and the retained common reserve. Invalid sparse literal codes begin
as actual zero-polynomial entries. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomInitialize
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NativeIndexedAtom (heads data)

def widthSlot : Fin 1→Fin 45 := ![24]
def allocateSlots : Fin 4→Fin 45 := ![33,42,43,24]
noncomputable def up := RecoveryFocus.machine widthSlot (Completion.PhysicalDriverMoves.machine 1 .right)
noncomputable def down := RecoveryFocus.machine widthSlot (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def allocate := RecoveryFocus.machine allocateSlots PhysicalZeroBank.machine
noncomputable def machine := Composition.machine up (Composition.machine allocate down)

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomInitialize
