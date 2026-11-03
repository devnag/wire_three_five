import Proof.Packets.ReusableArithmeticCore

/-! Executed scratch clearing and the complete reusable arithmetic cycle. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound

def scratch : Fin 24 → Fin 30 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,14,15,16,17,18,19,20,21,22,23,29]
def eraseSlots (i : Fin 26) : Fin 34 :=
  Fin.addCases (fun j : Fin 24=>(scratch j).castAdd 4) (![32,33] : Fin 2 → Fin 34) i
noncomputable def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 24)

noncomputable def machine {s : Nat} (p : Machine 30 s) :=
  Composition.machine (Composition.machine (Composition.machine (worker p)
    (copyMachine 20 26)) (copyMachine 21 27)) eraseMachine

end PCJ9eff70d512234a4c_Fixed.Materializer.ReusableArithmetic
