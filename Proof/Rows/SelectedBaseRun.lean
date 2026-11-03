import Proof.Rows.SelectedBase

/-! The consumed reusable selected-child base update. No semantic gate or
arity template is assumed as input: the circuit payload supplies both. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_SelectedBaseRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open PCJ45bee56da9f34d5a_SelectedBase
noncomputable section

def budget {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w C U : Nat):=
  2*PCPPQueryNatural.budget n+PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+
    C10ThresholdSelectedChild.budget (gs.get i) U+4*n+18*U+
    C10ThresholdChildMagnitude.budget (gs.get i) w C+16*(w+2)+93

theorem run {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w C D U a : Nat)
    (hu : PCPPQueryNatural.budget n<U)
    (hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
    (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
    (hg : (exactWord (gs.get i)).length+2≤U)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items (gs.get i),natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude (gs.get i)<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items (gs.get i)) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude (gs.get i)+a<2^(w+2))
    (hF : C10ThresholdChildMagnitude.budget (gs.get i) w C+2≤U)
    (hU : ∀ j,(Base.words (ZeroPadding.pad U (exactWord (gs.get i))) (List.replicate (n+1) true)
      (n+1) w C U a j).length≤U) :
    Step machine (budget gs i w C U)
      (heads 0) (bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
        (List.replicate U false) (List.replicate U false) i.val w C U a)
      (heads 0) (bank (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
        (List.replicate U false) (List.replicate U false) i.val w C U (childMagnitude (gs.get i)+a)):=by
  have hn:n+2≤U:=by unfold PCPPQueryNatural.budget MatrixDimensionPrepare.budget at hu;omega
  have first:=read_run gs i.val w C U a hu
  have second:=select_run gs i w C U a hp hf hg
  have third:=evaluate_run (gs.get i) (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
    i.val w C D U a hw hc hm hD hC hDU ha hF hU
  have hg' : (exactWord gs[i.val]).length≤U:=by simpa only [List.get_eq_getElem] using (show (exactWord (gs.get i)).length≤U by omega)
  have last:=wipe_run (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
    (ZeroPadding.pad U (exactWord (gs.get i))) (ZeroPadding.pad U (UnaryTemplate.tape n))
    i.val w C U (childMagnitude (gs.get i)+a)
    (by simp [ZeroPadding.pad_length];omega) (by simp [ZeroPadding.pad_length,UnaryTemplate.tape];omega)
  have all:=((first.seq second).seq third).seq last
  unfold machine
  convert all using 1
  unfold budget
  omega

end
end PCJ45bee56da9f34d5a_SelectedBaseRun
