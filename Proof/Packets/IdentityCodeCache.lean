import Proof.Packets.IdentityCodeLoop
import Proof.Packets.PhysicalCounterCopy
import Proof.Packets.WindowSeedClear
import Proof.Packets.NativeIndexedAtom

/-! Closed reusable identity cache producer. It physically clears its two
private tapes, copies the retained actual count, emits every descending code,
and returns the output cursor. Blank and previously backed private tapes use
the same entry theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeCache
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def clearSlots : Fin 4→Fin 6 := ![0,1,4,5]
def backSlots : Fin 2→Fin 6 := ![3,1]
def clear := RecoveryFocus.machine clearSlots (RecoveryScratchErase.resetMachine 2)
def up := PhysicalIndexReload.move (0 : Fin 6) .right
def down := PhysicalIndexReload.move (0 : Fin 6) .left
def copy := PhysicalCounterCopy.machine (t:=6) 3 2 0
def loop := TapeEmbedding.machine 3 IdentityCodeLoop.machine
def back := RecoveryFocus.machine backSlots Completion.PhysicalBoundedLeftRewind.machine
def machine := Composition.machine clear (Composition.machine up (Composition.machine copy
  (Composition.machine loop (Composition.machine back down))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.IdentityCodeCache
