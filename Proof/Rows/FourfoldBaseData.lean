import Proof.Rows.DigitBaseRun

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
def Data.acc (d : Data) (j : Nat):=1+(d.values.take j).sum
@[simp] theorem words_length (d : Data):d.words.length=d.count:=by simp [Data.words]
@[simp] theorem values_length (d : Data):d.values.length=d.count:=by simp [Data.values]
theorem acc_zero (d : Data):d.acc 0=1:=rfl

theorem acc_next (d : Data) (j : Fin d.count):
    d.acc (j.val+1)=childMagnitude ((d.gates j).get (d.selected j))+d.acc j.val:=by
  unfold Data.acc
  rw [List.take_succ_eq_append_getElem (by simp),List.sum_append]
  simp only [Data.values,List.getElem_ofFn,List.sum_cons,List.sum_nil,add_zero]
  change 1+((d.values.take j.val).sum+childMagnitude ((d.gates j).get (d.selected j)))=
    childMagnitude ((d.gates j).get (d.selected j))+(1+(d.values.take j.val).sum)
  omega

theorem acc_absent (d : Data) (j : Nat) (hj : d.count ≤ j):d.acc (j+1)=d.acc j:=by
  simp only [Data.acc,List.take_of_length_le (show d.values.length ≤ j by simpa using hj),
    List.take_of_length_le (show d.values.length ≤ j+1 by simp;omega)]

theorem acc_four (d : Data):d.acc 4=1+d.values.sum:=by
  unfold Data.acc
  rw [List.take_of_length_le (by simpa using d.count_le)]

structure LocalBounds {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length)
    (v w C D U a : Nat) : Prop where
  digit_fit : i.val<2^v
  digit_cost : MatrixUnaryTemplate.budget v i.val<U
  arity_cost : PCPPQueryNatural.budget n<U
  payload_fit : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length ≤ U
  cursor_cost : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1 ≤ U
  gate_fit : (exactWord (gs.get i)).length+2 ≤ U
  weight_fit : ∀x∈C10ThresholdChildMagnitude.items (gs.get i),natBitLength x.1.natAbs ≤ w
  clock_fit : 8*w+12 ≤ C
  magnitude_fit : childMagnitude (gs.get i)<2^w
  score_cost : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items (gs.get i)) w C ≤ D
  clock_cap : C+1 ≤ U
  score_cap : D ≤ U
  result_fit : childMagnitude (gs.get i)+a<2^(w+2)
  magnitude_cost : C10ThresholdChildMagnitude.budget (gs.get i) w C+2 ≤ U
  masters_fit : ∀j,(PCJ45bee56da9f34d5a_SelectedBase.Base.words (ZeroPadding.pad U (exactWord (gs.get i)))
    (List.replicate (n+1) true) (n+1) w C U a j).length ≤ U

structure Bounds (d : Data) (v w C D U B F : Nat) : Prop where
  payloads : ∀x∈d.words,x.length ≤ B
  top_cost : ∀j : Fin d.words.length,PCJ45bee56da9f34d5a_TopFrameReentry.budget d.words j B+2 ≤ U
  local_fit : ∀j : Fin d.count,LocalBounds (d.gates j) (d.selected j) v w C D U (d.acc j.val)
  cell_cost : ∀j : Fin d.count,PCJ45bee56da9f34d5a_DigitBaseRun.budget d.words
    ⟨j.val,by simp⟩ B (d.gates j) (d.selected j) v w C U ≤ F
end
end PCJ45bee56da9f34d5a_FourfoldBaseData
