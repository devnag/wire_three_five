import Proof.Rows.HeaderErase

/-! Physically rewind bounded dirty Header heads before the scratch sweep.
The unary U driver is scanned once; only its own head needs the recorded
return pass. No tape content is changed, and the cap driver/log are reusable.
-/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
namespace PCJ45bee56da9f34d5a_HeaderRewind
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.RecoveryExecution

variable (t : Nat)

def raw : Machine (t+1) 2 where
  descriptionBits := 0
  start := 0
  halted := fun q=>q.val==1
  rule := fun q scanned=>if q.val=0 then
    if scanned ((0 : Fin 1).natAdd t) then some ⟨0,fun _=>none,
      Fin.addCases (fun _ : Fin t=>.left) (fun _ : Fin 1=>.right)⟩
    else some ⟨1,fun _=>none,fun _=>.stay⟩
    else none

def selected : Fin (t+1)→Bool := Fin.addCases (fun _ : Fin t=>false) (fun _ : Fin 1=>true)
def machine := MaskedReset.machine (raw t) (selected t)


def clear := Composition.machine (machine t) (RecoveryScratchErase.resetMachine t)

open NearCubicWires.P1Closure NearCubicWires.RepairRepresentation PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_HeaderErase
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

end

end PCJ45bee56da9f34d5a_HeaderRewind
