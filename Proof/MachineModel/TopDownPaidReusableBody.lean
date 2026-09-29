import Proof.MachineModel.ClosureActualRawRow
import Proof.MachineModel.TopDownPaidReloadStream

/-! A complete advancing-stream transaction around the existing row worker.
The fixed tape-order source contains cold entry words, never an answer.
The simultaneous final erase has one linear shared-capacity charge. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace NearCubicWires.P1TopDownPaidReusableBody
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch RecoveryRootRound P1Closure
namespace Loader
open P1TopDownPaidReloadStream
end Loader

def heads (t pos : Nat) (out : List Bool) : Fin (t+1+2+4)→Nat :=
  Fin.addCases (RawRowJoin.heads t out) ![pos,0,0,0]
def bank {t : Nat} (A : Fin t→List Bool) (source : List Bool) (S R B : Nat) (out : List Bool) :
    Fin (t+1+2+4)→List Bool :=
  Fin.addCases (RawRowJoin.bank A R B out)
    ![source,List.replicate S false,List.replicate S true,List.replicate (S+1) false]
def loadSlots (t : Nat) : Fin (t+2)→Fin (t+1+2+4) :=
  Fin.addCases (fun i : Fin t=>(i.castAdd 1).castAdd 2 |>.castAdd 4)
    ![(0 : Fin 4).natAdd (t+1+2),(1 : Fin 4).natAdd (t+1+2)]
def eraseSlots (t : Nat) : Fin (t+1+1)→Fin (t+1+2+4) :=
  Fin.addCases (Fin.addCases (fun i : Fin t=>(i.castAdd 1).castAdd 2 |>.castAdd 4)
    (fun _ : Fin 1=>(2 : Fin 4).natAdd (t+1+2)))
    (fun _ : Fin 1=>(3 : Fin 4).natAdd (t+1+2))

noncomputable def load (t : Nat) := RecoveryFocus.machine (loadSlots t)
  (P1TopDownPaidReloadStream.machine (List.finRange t))
noncomputable def erase (t : Nat) := RecoveryFocus.machine (eraseSlots t) (RecoveryScratchErase.resetMachine t)
noncomputable def machine {t st : Nat} (worker : Machine (t+1+2) st) :=
  Composition.machine (Composition.machine (load t) (TapeEmbedding.machine 4 worker)) (erase t)
def word {t : Nat} (A : Fin t→List Bool) := P1TopDownPaidReloadStream.stream A (List.finRange t)

end NearCubicWires.P1TopDownPaidReusableBody
