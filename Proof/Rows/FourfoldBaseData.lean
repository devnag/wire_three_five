import Proof.Rows.CellGatePalette
import Proof.Rows.HeaderRewind
import Proof.Rows.TopChildCursor

/-! Finite semantic data and numerical bounds for the four concrete calls.
Every physical operation is the already consumed DigitBaseRun machine. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_FourfoldBaseData
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
noncomputable section

structure Data where
  count : Nat
  arity : Fin count→Nat
  gates : (j : Fin count)→List (ExactThresholdGate (arity j))
  selected : (j : Fin count)→Fin (gates j).length
  count_le : count ≤ 4

def Data.words (d : Data):=List.ofFn (fun j=>PCJ45bee56da9f34d5a_TopChildCursor.payload (d.gates j))
def Data.values (d : Data):=List.ofFn (fun j=>childMagnitude ((d.gates j).get (d.selected j)))
def Data.digits (d : Data) (j : Fin 4):=if h:j.val<d.count then (d.selected ⟨j.val,h⟩).val else 0
@[simp] theorem words_length (d : Data):d.words.length=d.count:=by simp [Data.words]

end
end PCJ45bee56da9f34d5a_FourfoldBaseData
