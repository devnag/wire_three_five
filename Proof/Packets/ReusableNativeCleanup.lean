import Proof.Packets.ReusableNativeCore

/-! Executed scratch clearing and the complete reusable arithmetic cycle. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound

def scratch : Fin 28 → Fin 32 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18,19,20,21,22,23,25,28,29,30,31]
def eraseSlots (i : Fin 30) : Fin 36 :=
  Fin.addCases (fun j : Fin 28=>(scratch j).castAdd 4) (![34,35] : Fin 2 → Fin 36) i
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 28)

noncomputable def machine {s : Nat} (p : Machine 32 s) :=
  Composition.machine (Composition.machine (Composition.machine (worker p)
    (copyMachine 20 26)) (copyMachine 21 27)) eraseMachine

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableNative
