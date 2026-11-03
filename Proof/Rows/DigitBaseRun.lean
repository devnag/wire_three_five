import Proof.Rows.DigitBaseInput

/-! Actual framed top request plus one binary child digit updates the canonical
base and restores every temporary tape, including the unary child locator. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_DigitBaseRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open PCJ45bee56da9f34d5a_DigitBaseInput
noncomputable section

def budget {n : Nat} (words : List (List Bool)) (circuit : Fin words.length) (B : Nat)
    (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (v w C U : Nat):=
  PCJ45bee56da9f34d5a_CircuitBaseRun.budget words circuit B gs i w C U+
    MatrixUnaryTemplate.budget v i.val+4*U+13

theorem run (words : List (List Bool)) (circuit : Fin words.length) (B : Nat) {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (v w C D U a : Nat)
    (hi : i.val<2^v) (hv : MatrixUnaryTemplate.budget v i.val<U)
    (hb : ∀x∈words,x.length≤B)
    (htop : PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit B+2≤U)
    (hselected : words.get circuit=PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
    (hu : PCPPQueryNatural.budget n<U)
    (hp : (PCJ45bee56da9f34d5a_TopChildCursor.payload gs).length≤U)
    (hf : PCJ45bee56da9f34d5a_TopChildCursor.budget gs i.val+1≤U)
    (hg : (exactWord (gs.get i)).length+2≤U)
    (hw : ∀ x∈C10ThresholdChildMagnitude.items (gs.get i),natBitLength x.1.natAbs≤w)
    (hc : 8*w+12≤C) (hm : childMagnitude (gs.get i)<2^w)
    (hD : C10NaturalHardwireScore.loopBudget (C10ThresholdChildMagnitude.items (gs.get i)) w C≤D)
    (hC : C+1≤U) (hDU : D≤U) (ha : childMagnitude (gs.get i)+a<2^(w+2))
    (hF : C10ThresholdChildMagnitude.budget (gs.get i) w C+2≤U)
    (hU : ∀ j,(PCJ45bee56da9f34d5a_SelectedBase.Base.words (ZeroPadding.pad U (exactWord (gs.get i))) (List.replicate (n+1) true)
      (n+1) w C U a j).length≤U) :
    Step machine (budget words circuit B gs i v w C U)
      (heads 0) (bank (words.flatMap frame) (List.replicate U false) circuit.val i.val v w C U a)
      (heads 0) (bank (words.flatMap frame) (List.replicate U false) circuit.val i.val v w C U
        (childMagnitude (gs.get i)+a)):=by
  have first:=prepare_run (words.flatMap frame) circuit.val i.val v w C U a hi hv
  have middle:=(PCJ45bee56da9f34d5a_CircuitBaseRun.run words circuit B gs i w C D U a hb htop hselected
    hu hp hf hg hw hc hm hD hC hDU ha hF hU).embed (fun _ : Fin 2=>0)
      (![List.replicate v true,frame (SignedSortKey.binary v i.val)] : Fin 2→List Bool)
  simp only [prepared_eq,prepared_heads] at middle
  have ilen:i.val+2≤U:=by unfold MatrixUnaryTemplate.budget at hv;omega
  have last:=clear_run (words.flatMap frame) (ZeroPadding.pad U (UnaryTemplate.tape i.val))
    circuit.val i.val v w C U (childMagnitude (gs.get i)+a)
    (by simp [ZeroPadding.pad_length,UnaryTemplate.tape];omega)
  have all:=(first.seq middle).seq last
  unfold machine evaluate
  convert all using 1
  unfold budget
  omega
end
end PCJ45bee56da9f34d5a_DigitBaseRun
