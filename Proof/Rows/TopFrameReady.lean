import Proof.Rows.TopFrame
import Proof.Rows.SelectedBaseRun

/-! Reusable outer circuit extraction. The original framed topWord survives;
all temporary decoding tapes are erased, retaining the padded chosen payload. -/
set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_TopFrameReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.VerifierDecoding
open PCJ45bee56da9f34d5a_TopFrame
noncomputable section

theorem retained_run (words : List (List Bool)) (i : Fin words.length) (B : Nat)
    (hb : ∀ x∈words,x.length≤B) :
    ∃ H A,Step PCJ45bee56da9f34d5a_TopFrame.machine
      (4*(words.flatMap frame).length+CloseoutRowsTouching.FrameSeek.budget B i.val+8*(words.get i).length+11)
      (heads 0) (input (words.flatMap frame) i.val) H A ∧
      H 6=0 ∧ A 6=words.get i ∧ A 0=frame (words.flatMap frame) ∧ A 3=CompareMachine.word i.val:=by
  have split:=CloseoutRowsFamilyLoop.split_word words [] frame i.val i.isLt
  have get : words.getD i.val []=words.get i:=by
    rw [List.getD_eq_getElem _ [] i.isLt];rfl
  rw [get] at split
  let pre:=(words.take i.val).flatMap frame
  let bits:=words.get i
  have copied:=copy_run pre bits ((words.drop (i.val+1)).flatMap frame) i.val
  change Step copy _ _ (bank ((words.take i.val).flatMap frame++frame (words.get i)++
      (words.drop (i.val+1)).flatMap frame) i.val [] [] [] [])
    _ (copyBank ((words.take i.val).flatMap frame++frame (words.get i)++
      (words.drop (i.val+1)).flatMap frame) bits i.val) at copied
  rw [←split] at copied
  have decoded:=decode_run bits (copyHead pre bits) (copyBank (words.flatMap frame) bits i.val)
    (by
      intro j;fin_cases j
      · exact dockH_slot copySlots copy_injective _ _ 1
      · exact (dockH_other copySlots _ _ _ (by decide)).trans rfl
      · exact (dockH_other copySlots _ _ _ (by decide)).trans rfl)
    (by
      intro j;fin_cases j
      · exact install_slot copySlots copy_injective _ _ 1
      · exact (install_other copySlots _ _ _ (by decide)).trans rfl
      · exact (install_other copySlots _ _ _ (by decide)).trans rfl)
  have h:=(unwrap_run (words.flatMap frame) i.val).seq
    ((seek_run words i.val B (Nat.le_of_lt i.isLt) hb).seq (copied.seq decoded))
  have cost : (4*(words.flatMap frame).length+2)+1+
      (CloseoutRowsTouching.FrameSeek.budget B i.val+1+
      ((2*(frame bits).length+2)+1+(4*bits.length+2)))=
      4*(words.flatMap frame).length+CloseoutRowsTouching.FrameSeek.budget B i.val+
        8*(words.get i).length+11:=by rw [frame_length];dsimp only [bits];omega
  rw [cost] at h
  refine ⟨_,_,h,?_,?_,?_,?_⟩
  · exact dockH_slot decodeSlots (by decide) _ _ 1
  · exact install_slot decodeSlots (by decide) _ _ 1
  · exact (install_other decodeSlots _ _ 0 (by decide)).trans
      ((install_other copySlots _ _ 0 (by decide)).trans rfl)
  · exact (install_other decodeSlots _ _ 3 (by decide)).trans
      ((install_other copySlots _ _ 3 (by decide)).trans rfl)
end
end PCJ45bee56da9f34d5a_TopFrameReady
