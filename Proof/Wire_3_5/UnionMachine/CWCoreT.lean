import Proof.Wire_3_5.UnionMachine.CWCore
import Proof.Wire_3_5.UnionMachine.CWRoundT

/-! # C6 front, U5, the code writers: the `THR∘THR` carrier core's layout

The `THR∘THR` carrier core is FP's carrier core (`CWCore`, `CWMain`) with loop A replaced by the `THR∘THR` loop
(`CWRoundT.foldT`: the retained bottoms only). Its round has `743` tapes instead of `423`, so the core has `1233`
tapes: FP's `913` in FP's places, and the `320` extra round tapes of the loop on `913..1232`.

Paper quantity: none (the layout of the `THR∘THR` carrier writer). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWCoreT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (addCases_val)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)
open NearCubicWires.WireExponent3_5.Transfer

/-! ## The layout (1233 tapes)

FP's layout (`CWCore`), with loop A's `423` round tapes on `0, 71, 72, 69, 73..491` as before and the `THR∘THR` round's
further `320` tapes on `913..1232`; its erase clears `71`, `73..491` and `913..1232`. -/

def cellSl : Fin 1 → Fin 1233 := fun _ => 2
def lenSl : Fin 4 → Fin 1233 := ![0, 2, 3, 4]
def cntSl : Fin 5 → Fin 1233 := ![0, 2, 5, 6, 7]
def polySl (j : Fin 62) : Fin 1233 := ⟨if j.val = 0 then 3 else j.val + 7, by split_ifs <;> omega⟩
def initSl : Fin 3 → Fin 1233 := ![69, 2, 70]
def erTSl (j : Fin (740 + 1 + 1)) : Fin 1233 :=
  ⟨if j.val = 0 then 71 else if j.val < 420 then j.val + 72 else if j.val < 740 then j.val + 493
    else if j.val = 740 then 58 else 492, by split_ifs <;> omega⟩
def foldTSl (j : Fin (743 + 2 + 1)) : Fin 1233 :=
  ⟨if j.val = 0 then 0 else if j.val = 1 then 71 else if j.val = 2 then 72 else if j.val = 3 then 69
    else if j.val < 423 then j.val + 69 else if j.val < 743 then j.val + 490 else if j.val = 743 then 58
    else if j.val = 744 then 492 else 5,
    by split_ifs <;> omega⟩
def erBSl (j : Fin (290 + 1 + 1)) : Fin 1233 :=
  ⟨if j.val = 0 then 493 else if j.val < 290 then j.val + 494 else if j.val = 290 then 58 else 492, by split_ifs <;> omega⟩
def foldBSl (j : Fin (292 + 2 + 1)) : Fin 1233 :=
  ⟨if j.val = 0 then 72 else if j.val = 1 then 493 else if j.val = 2 then 494
    else if j.val < 292 then j.val + 492 else if j.val = 292 then 58 else if j.val = 293 then 492 else 69,
    by split_ifs <;> omega⟩
def serSl (j : Fin 129) : Fin 1233 :=
  ⟨if j.val = 0 then 494 else if j.val = 2 then 69 else if j.val = 1 then 784 else j.val + 782, by split_ifs <;> omega⟩
def natSl : Fin 5 → Fin 1233 := ![859, 2, 1, 911, 912]

theorem cellSl_inj : Function.Injective cellSl := fun a b _ => Subsingleton.elim a b
theorem lenSl_inj : Function.Injective lenSl := by decide
theorem cntSl_inj : Function.Injective cntSl := by decide
theorem initSl_inj : Function.Injective initSl := by decide
theorem natSl_inj : Function.Injective natSl := by decide
theorem polySl_inj : Function.Injective polySl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [polySl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem erTSl_inj : Function.Injective erTSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [erTSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
set_option maxHeartbeats 2000000 in
theorem foldTSl_inj : Function.Injective foldTSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [foldTSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem erBSl_inj : Function.Injective erBSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [erBSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem foldBSl_inj : Function.Injective foldBSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [foldBSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega
theorem serSl_inj : Function.Injective serSl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [serSl] at hv
  have := a.isLt; have := b.isLt; apply Fin.ext; split_ifs at hv <;> omega

theorem lenSl_val (j : Fin 4) : (lenSl j).val = [0, 2, 3, 4].getD j.val 0 := by fin_cases j <;> rfl
theorem cntSl_val (j : Fin 5) : (cntSl j).val = [0, 2, 5, 6, 7].getD j.val 0 := by fin_cases j <;> rfl
theorem initSl_val (j : Fin 3) : (initSl j).val = [69, 2, 70].getD j.val 0 := by fin_cases j <;> rfl
theorem natSl_val (j : Fin 5) : (natSl j).val = [859, 2, 1, 911, 912].getD j.val 0 := by fin_cases j <;> rfl

/-! ## Misses -/

section Miss
variable (A : Fin 1233 → List Bool) (t : Fin 1233)

theorem miss_cell (h : t.val ≠ 2) (o : Fin 1 → List Bool) : install cellSl A o t = A t :=
  install_other _ _ _ _ (fun _ e => h (by rw [← e]; rfl))
theorem miss_len (h : t.val ≠ 0 ∧ t.val ≠ 2 ∧ t.val ≠ 3 ∧ t.val ≠ 4) (o : Fin 4 → List Bool) : install lenSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [lenSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_cnt (h : t.val ≠ 0 ∧ t.val ≠ 2 ∧ t.val ≠ 5 ∧ t.val ≠ 6 ∧ t.val ≠ 7) (o : Fin 5 → List Bool) :
    install cntSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [cntSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_poly (h : t.val ≠ 3 ∧ (t.val < 8 ∨ 69 ≤ t.val)) (o : Fin 62 → List Bool) : install polySl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [polySl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_init (h : t.val ≠ 69 ∧ t.val ≠ 2 ∧ t.val ≠ 70) (o : Fin 3 → List Bool) : install initSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [initSl_val] at hv; fin_cases j <;> simp at hv <;> omega)
theorem miss_erT (h : t.val ≠ 71 ∧ t.val ≠ 58 ∧ t.val ≠ 492 ∧ (t.val < 73 ∨ (492 ≤ t.val ∧ t.val < 913)))
    (o : Fin (740 + 1 + 1) → List Bool) : install erTSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [erTSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_foldT (h : t.val ≠ 0 ∧ t.val ≠ 5 ∧ t.val ≠ 58 ∧ t.val ≠ 69 ∧ t.val ≠ 492 ∧
    (t.val < 71 ∨ (492 ≤ t.val ∧ t.val < 913)))
    (o : Fin (743 + 2 + 1) → List Bool) : install foldTSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [foldTSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_erB (h : t.val ≠ 493 ∧ t.val ≠ 58 ∧ t.val ≠ 492 ∧ (t.val < 495 ∨ 784 ≤ t.val))
    (o : Fin (290 + 1 + 1) → List Bool) : install erBSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [erBSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_foldB (h : t.val ≠ 72 ∧ t.val ≠ 58 ∧ t.val ≠ 69 ∧ t.val ≠ 492 ∧ (t.val < 493 ∨ 784 ≤ t.val))
    (o : Fin (292 + 2 + 1) → List Bool) : install foldBSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [foldBSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_ser (h : t.val ≠ 494 ∧ t.val ≠ 69 ∧ (t.val < 784 ∨ 911 ≤ t.val)) (o : Fin 129 → List Bool) :
    install serSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; simp only [serSl] at hv; have := j.isLt; split_ifs at hv <;> omega)
theorem miss_nat (h : t.val ≠ 859 ∧ t.val ≠ 2 ∧ t.val ≠ 1 ∧ t.val ≠ 911 ∧ t.val ≠ 912) (o : Fin 5 → List Bool) :
    install natSl A o t = A t :=
  install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e; rw [natSl_val] at hv; fin_cases j <;> simp at hv <;> omega)

end Miss

/-! ## The loop's bank -/

/-- The `THR∘THR` loop's bank at circuit `i`, by tape. -/
theorem foldBankT_val (xs : List ℕ) (T i c : ℕ) (j : Fin (743 + 2 + 1)) :
    Fin.addCases (m := 743 + 2) (n := 1) (motive := fun _ => List Bool)
      (roundTapes (padScratch CWRoundT.scrT T (CWRoundT.Qt xs T i)) T (T + 1)) (fun _ => CompareMachine.word c) j =
    if j.val = 0 then (xs.map nf).flatten ++ [false]
    else if j.val = 1 then ZeroPadding.pad T (List.replicate i true)
    else if j.val = 2 then (CWRoundT.bacT xs i).flatMap frame
    else if j.val = 3 then false :: List.replicate (CWRoundT.bacT xs i).length true
    else if j.val < 743 then List.replicate T false
    else if j.val = 743 then List.replicate T true
    else if j.val = 744 then List.replicate (T + 1) false
    else CompareMachine.word c := by
  rw [addCases_val]
  by_cases h1 : j.val < 743 + 2
  · rw [dif_pos h1]; unfold roundTapes; rw [addCases_val]
    by_cases h2 : j.val < 743
    · rw [dif_pos h2]
      unfold padScratch scratchCap
      by_cases h3 : 4 ≤ j.val
      · rw [if_pos ((CWRoundT.scrT_iff ⟨j.val, h2⟩).mpr h3)]
        simp only [CWRoundT.Qt, CWRoundT.roundTIn]
        have e0 : j.val ≠ 0 := by omega
        have e1 : j.val ≠ 1 := by omega
        have e2 : j.val ≠ 2 := by omega
        have e3 : j.val ≠ 3 := by omega
        simp [e0, e1, e2, e3, h2, ZeroPadding.pad]
      · rw [if_neg (fun hh => h3 ((CWRoundT.scrT_iff ⟨j.val, h2⟩).mp hh))]
        simp only [CWRoundT.Qt, CWRoundT.roundTIn, ZeroPadding.pad_zero]
        have : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 := by omega
        rcases this with e | e | e | e <;> simp [e]
    · rw [dif_neg h2]
      have : j.val = 743 ∨ j.val = 744 := by omega
      rcases this with e | e <;> simp [e]
  · rw [dif_neg h1]
    have e : j.val = 745 := by omega
    simp [e]

end NearCubicWires.WireExponent3_5.UnionMachine.CWCoreT
