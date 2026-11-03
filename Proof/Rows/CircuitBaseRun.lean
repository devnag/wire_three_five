import Proof.Rows.CircuitBaseInput

/-! One actual selected circuit updates the exact base and returns the outer
framed request, the circuit and child cursors, and all temporary tapes ready. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_CircuitBaseRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open PCJ45bee56da9f34d5a_CircuitBaseInput
noncomputable section

def budget {n : Nat} (words : List (List Bool)) (circuit : Fin words.length) (B : Nat)
    (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w C U : Nat):=
  PCJ45bee56da9f34d5a_TopFrameReentry.budget words circuit B+
    PCJ45bee56da9f34d5a_SelectedBaseRun.budget gs i w C U+6*U+18

theorem run (words : List (List Bool)) (circuit : Fin words.length) (B : Nat) {n : Nat} (gs : List (ExactThresholdGate n)) (i : Fin gs.length) (w C D U a : Nat)
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
    Step machine (budget words circuit B gs i w C U)
      heads (bank (words.flatMap frame) [] circuit.val i.val w C U a)
      heads (bank (words.flatMap frame) [] circuit.val i.val w C U (childMagnitude (gs.get i)+a)):=by
  have first:=extract_run words circuit B i.val w C U a hb htop
  rw [hselected] at first
  have update:=((PCJ45bee56da9f34d5a_SelectedBaseRun.run gs i w C D U a hu hp hf hg hw hc hm hD
    hC hDU ha hF hU).pad (caps U)).embed (![0,1] : Fin 2→Nat)
      (![frame (words.flatMap frame),ZeroPadding.pad U (CompareMachine.word circuit.val)] : Fin 2→List Bool)
  have middle:Step evaluate (PCJ45bee56da9f34d5a_SelectedBaseRun.budget gs i w C U)
      heads (bank (words.flatMap frame) (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) circuit.val i.val w C U a)
      heads (bank (words.flatMap frame) (PCJ45bee56da9f34d5a_TopChildCursor.payload gs) circuit.val i.val w C U
        (childMagnitude (gs.get i)+a)):=update
  have last:=wipe_run (words.flatMap frame) (PCJ45bee56da9f34d5a_TopChildCursor.payload gs)
    circuit.val i.val w C U (childMagnitude (gs.get i)+a) hp
  have all:=(first.seq middle).seq last
  unfold machine
  convert all using 1
  unfold budget
  omega
end
end PCJ45bee56da9f34d5a_CircuitBaseRun
