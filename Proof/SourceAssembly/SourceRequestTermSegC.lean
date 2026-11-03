import Proof.SourceAssembly.SourceRequestTermSegB
import Proof.MachineModel.ClockNormalize

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.TermSegC
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.TermSeg

def pS (i : Fin 149) : Fin 155 := ⟨1 + i.val, by omega⟩
def c1S : Fin 3 → Fin 155 := ![0, 2, 150]
def nS : Fin 5 → Fin 155 := ![151, 79, 152, 153, 154]


noncomputable def machine :=
  Composition.machine
    (Composition.machine (RecoveryFocus.machine c1S copyMachine)
      (RecoveryFocus.machine pS CloseoutWitness.PairHeader.machine))
    (RecoveryFocus.machine nS ClockNormalize.machine)

def cost (n cwid : Nat) : Nat := ((2 * (2 * n + 1) + 2) + 1 + 28000 * (n + 1) ^ 2) + 1 + (4 * cwid + 4)

end NearCubicWires.SourceRequest.TermSegC

