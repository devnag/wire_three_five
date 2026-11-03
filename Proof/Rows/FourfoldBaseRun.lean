import Proof.Rows.FourfoldBaseGuard
import Proof.Rows.FourfoldBaseData

/-! Four guarded real native circuit calls compute one plus the exact sum of
selected-child magnitudes and restore the shared count/cursor bank. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_FourfoldBaseRun
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.ThresholdAlignedEnvelope
open PCJ45bee56da9f34d5a_FourfoldBaseCell PCJ45bee56da9f34d5a_FourfoldBaseData
open PCJ45bee56da9f34d5a_FourfoldBaseGuard
noncomputable section

def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine (phase 0) (phase 1)) (phase 2)) (phase 3)) restore

theorem phase_run (d : Data) (v w C D U B F : Nat) (hb : Bounds d v w C D U B F) (j : Fin 4):
    Step (phase j) (F+4) (heads (j.val+1)) (bank (d.words.flatMap frame) d.digits d.count v w C U (d.acc j.val))
      (heads (j.val+2)) (bank (d.words.flatMap frame) d.digits d.count v w C U (d.acc (j.val+1))):=by
  by_cases hj:j.val<d.count
  · let k:Fin d.count:=⟨j.val,hj⟩
    let circuit:Fin d.words.length:=⟨j.val,by simpa using hj⟩
    have hlocal:=hb.local_fit k
    have chosen:d.words.get circuit=PCJ45bee56da9f34d5a_TopChildCursor.payload (d.gates k):=by
      simp [Data.words,List.get_eq_getElem,circuit,k]
    have digit:d.digits j=(d.selected k).val:=by simp [Data.digits,hj,k]
    have first:=true_run j d.digits d.words circuit B (d.gates k) (d.selected k) v w C D U (d.acc j.val)
      rfl digit hlocal.digit_fit hlocal.digit_cost hb.payloads (hb.top_cost circuit) chosen
      hlocal.arity_cost hlocal.payload_fit hlocal.cursor_cost hlocal.gate_fit hlocal.weight_fit
      hlocal.clock_fit hlocal.magnitude_fit hlocal.score_cost hlocal.clock_cap hlocal.score_cap
      hlocal.result_fit hlocal.magnitude_cost hlocal.masters_fit
    have more:PCJ45bee56da9f34d5a_DigitBaseRun.budget d.words circuit B (d.gates k) (d.selected k) v w C U+2 ≤ F+2:=by
      have h:=hb.cell_cost k
      exact Nat.add_le_add_right h 2
    have next:childMagnitude ((d.gates k).get (d.selected k))+d.acc j.val=d.acc (j.val+1):=(acc_next d k).symm
    rw [next] at first
    simp only [words_length] at first
    exact (first.enlarge more).seq (advance_run (d.words.flatMap frame) d.digits d.count v w C U (d.acc (j.val+1)) (j.val+1))
  · have hcount:d.count ≤ j.val:=by omega
    have first:=false_run j (d.words.flatMap frame) d.digits d.count v w C U (d.acc j.val) hcount
    have last:=advance_run (d.words.flatMap frame) d.digits d.count v w C U (d.acc j.val) (j.val+1)
    rw [acc_absent d j.val hcount]
    exact (first.enlarge (show 2 ≤ F+2 by omega)).seq last

theorem run (d : Data) (v w C D U B F : Nat) (hb : Bounds d v w C D U B F):
    Step machine (4*F+27) (heads 1) (bank (d.words.flatMap frame) d.digits d.count v w C U 1)
      (heads 1) (bank (d.words.flatMap frame) d.digits d.count v w C U (1+d.values.sum)):=by
  have all:=((((phase_run d v w C D U B F hb 0).seq (phase_run d v w C D U B F hb 1)).seq
    (phase_run d v w C D U B F hb 2)).seq (phase_run d v w C D U B F hb 3)).seq
      (restore_run (d.words.flatMap frame) d.digits d.count v w C U (d.acc 4))
  rw [show d.acc ((0 : Fin 4).val) = 1 from acc_zero d,acc_four] at all
  unfold machine
  convert all using 1 <;> first | rfl | omega
end
end PCJ45bee56da9f34d5a_FourfoldBaseRun
