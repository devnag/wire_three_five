import Proof.Packets.NativeAtomStore

/-! Pay the index head return and clear both delivered operand blocks and
the decoded index after storage, retaining all cache/bank cursors. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairOrdinary.RecoveryRootRound

def indexSlot : Fin 1→Fin 44 := ![41]
def clearSlots : Fin 5→Fin 44 := ![26,27,41,34,35]
noncomputable def indexDown := RecoveryFocus.machine indexSlot (Completion.PhysicalDriverMoves.machine 1 .left)
noncomputable def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 3)
noncomputable def cleanup := Composition.machine indexDown clear

end PCJ9eff70d512234a4c_Fixed.Materializer.NativeAtomStore
