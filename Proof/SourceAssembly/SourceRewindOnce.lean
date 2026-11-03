import Proof.SourceAssembly.SourceRowWidth

section
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary
open RepairOrdinary.RecoveryRootRound
namespace NearCubicWires.SourceConstruction.RewindOnce
noncomputable section

def c1 : Fin 4 → Fin 7 := ![0, 1, 2, 3]
def c2 : Fin 4 → Fin 7 := ![0, 4, 5, 6]
def mask : Fin 7 → Bool := fun i => i.val = 5

def machine :=
  Composition.machine (Composition.machine
    (RecoveryFocus.machine c1 ClockUnarySum.machine)
    (RecoveryFocus.machine c2 ClockUnarySum.machine))
    (CloseoutWitness.SelectedErase.machine mask (2 : Fin 7) (3 : Fin 7))

def cost (V : ℕ) : ℕ := ((2*V+6)+1+(2*V+6))+1+(2*V+4)


end
end NearCubicWires.SourceConstruction.RewindOnce
end
