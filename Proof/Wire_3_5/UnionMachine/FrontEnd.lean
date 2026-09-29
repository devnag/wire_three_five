import Proof.Wire_3_5.UnionMachine.FrontPw

/-! # C6 front, the end: the admissibility check, then the loop bank or the rejecting bank

The front's last two stages (P3:3685-3691: "It rejects ... unless every call is admissible"; `Plan.bankA`):
* **`okW Pw`**: the table writer's word program run once for its admissibility bit `OK` (register `12`), which it
  writes on a flag stream; **`okStage_step`**: that program with its fill, rewound, docked on the worker's tapes (the
  writer's sources and the count shared, the rest on a region); the sources and the count are kept;
* **`endM`**: the check, then FinalPass's branch on the flag: the tail stage (`FrontTailStage.tailM`: the writer again,
  the capacities, the install, the erase) or the rejecting writer (`FrontGate.rejM`);
* **`endGood`**: `OK ≠ 0` → the loop bank at `capQ`, `RQ`, `RQ + 1`; **`endBad`**: `OK = 0` → the rejecting bank.

Paper quantity of the main types: the loop's entry bank (the valid branch) and the rejecting bank. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontEnd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

/-! ## The admissibility check's word program -/

section OKW

/-- **The check's program**: the writer's program on streams `0 … 10`, then `OK`'s bit on stream `11`. -/
def okW (Pw : WM 10 56) : WM 11 56 :=
  .seq (Pw.liftW Fin.castSucc id) (.ifr (12 : Fin 56) (.wr 11 true) (.wr 11 false))

/-- The writer's entry inside the check's layout. -/
def ωO (σT : WState 10 56) : WState 11 56 :=
  ⟨fun _ => 0, fun i => if h : i.val < 11 then σT.st ⟨i.val, h⟩ else [], fun _ => 0, σT.cell⟩

theorem okW_run (Pw : WM 10 56) (cap cap' : ℕ) (hcap : cap ≤ cap') (σT τT : WState 10 56) (n : ℕ)
    (hP : WExec cap Pw σT τT n) (hsT : ∀ i, σT.sh i = 0) (hvT : ∀ r, σT.val r = 0) :
    ∃ τ : WState 11 56, WExec cap' (okW Pw) (ωO σT) τ (n + 1 + (1 + 1)) ∧
      (∀ i : Fin 11, τ.st (Fin.castSucc i) = τT.st i) ∧ τ.st 11 = [decide (τT.val 12 ≠ 0)] := by
  have hl : LiftW Fin.castSucc id (ωO σT) σT :=
    ⟨fun i => (hsT i).symm,
     fun i => by
      show (if h : (Fin.castSucc i).val < 11 then σT.st ⟨(Fin.castSucc i).val, h⟩ else []) = σT.st i
      rw [dif_pos (by simp)]; rfl,
     fun r => (hvT r).symm, rfl⟩
  obtain ⟨ω1, e1, hl1, ho1⟩ := WExec.liftW cap cap' hcap Fin.castSucc (Fin.castSucc_injective _) id
    Function.injective_id hP (ωO σT) hl
  have hout : ∀ i : Fin 11, Fin.castSucc i ≠ (11 : Fin 12) := fun i h => by
    have e := congrArg Fin.val h; simp at e; omega
  have o11 := ho1.1 11 hout
  have st11 : ω1.st 11 = [] := by rw [o11.2]; rfl
  have sh11 : ω1.sh 11 = 0 := by rw [o11.1]; rfl
  have v12 : ω1.val 12 = τT.val 12 := hl1.val 12
  have kst : ∀ (b : Bool) (i : Fin 11),
      (ω1.sets 11 (writeTapeBit (ω1.st 11) (ω1.sh 11) b)).st (Fin.castSucc i) = τT.st i := fun b i => by
    simp only [WState.sets_st]; rw [Function.update_of_ne (hout i)]; exact hl1.st i
  by_cases hok : τT.val 12 = 0
  · have e2 := WExec.ifrF (cap := cap') (P := .wr 11 true) (r := (12 : Fin 56)) (by rw [v12]; exact hok)
      (WExec.wr (cap := cap') 11 false ω1)
    refine ⟨_, WExec.seq e1 e2, kst false, ?_⟩
    simp only [WState.sets_st, Function.update_self, st11, sh11, hok]
    rfl
  · have e2 := WExec.ifrT (cap := cap') (Q := .wr 11 false) (r := (12 : Fin 56)) (by rw [v12]; exact hok)
      (WExec.wr (cap := cap') 11 true ω1)
    refine ⟨_, WExec.seq e1 e2, kst true, ?_⟩
    simp only [WState.sets_st, Function.update_self, st11, sh11]
    simp [hok, writeTapeBit]

theorem wfIn_ωO (σT : WState 10 56) (W : ℕ) (j : Fin (WT 11 56)) :
    wfIn (ωO σT) W j = if j.val = 71 then List.replicate W true
      else if j.val = 0 then σT.st 0 else if h : 2 ≤ j.val ∧ j.val ≤ 11 then σT.st ⟨j.val - 1, by omega⟩ else [] := by
  rw [wfIn_val]
  by_cases h71 : j.val = 71
  · rw [if_pos (by omega), if_pos h71]
  · rw [if_neg (by omega), if_neg h71]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, if_pos h0]; rfl
    · rw [if_neg h0, if_neg h0]
      by_cases h1 : j.val = 1
      · rw [if_pos h1, dif_neg (by omega)]
      · rw [if_neg h1]
        by_cases h2 : 2 ≤ j.val ∧ j.val ≤ 11
        · rw [dif_pos (by omega), dif_pos h2]
          show (if h : j.val - 1 < 11 then σT.st ⟨j.val - 1, h⟩ else []) = _
          rw [dif_pos (by omega)]
        · rw [dif_neg h2]
          by_cases h3 : j.val ≤ 11 + 1
          · rw [dif_pos h3]
            show (if h : j.val - 1 < 11 then σT.st ⟨j.val - 1, h⟩ else []) = _
            rw [dif_neg (by omega)]
          · rw [dif_neg h3]

end OKW

/-! ## On the worker's tapes -/

section Stage
open NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontTail NearCubicWires.WireExponent3_5.UnionMachine.FrontTailStage
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- The check's shared tapes: the writer's sources and the count. -/
noncomputable def shO (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (j : Fin (WT 11 56)) :
    Option (Fin (NW P tf)) :=
  if h : 2 ≤ j.val ∧ j.val ≤ 11 then some (srcT ⟨j.val - 2, by omega⟩) else if j.val = 71 then some cntT else none

theorem shO_cases (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (j : Fin (WT 11 56)) (y : Fin (NW P tf))
    (h : shO P tf srcT cntT j = some y) :
    (∃ hj : 2 ≤ j.val ∧ j.val ≤ 11, y = srcT ⟨j.val - 2, by omega⟩) ∨ (j.val = 71 ∧ y = cntT) := by
  unfold shO at h
  split_ifs at h with h1 h2
  · exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
  · exact Or.inr ⟨h2, (Option.some.inj h).symm⟩

/-- **The check docked**: its fill, its program rewound, on a region at `k1`. -/
noncomputable def okM (Pw : WM 10 56) (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (k1 : ℕ)
    (hk1 : k1 + WT 11 56 ≤ tf) :=
  RecoveryFocus.machine (sl P tf (shO P tf srcT cntT) k1 hk1) (wfM (okW Pw))

/-- The flag's tape (the check's stream `11`). -/
noncomputable def flagT (k1 : ℕ) (hk1 : k1 + WT 11 56 ≤ tf) : Fin (NW P tf) :=
  rg P tf k1 hk1 ⟨12, by show 12 < 72; omega⟩

/-- **The front's end**: the check, then the tail stage (at `k0`) or the rejecting writer. -/
noncomputable def endM (Pw : WM 10 56) (cr K A : ℕ) (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf))
    (k1 : ℕ) (hk1 : k1 + WT 11 56 ≤ tf) (k0 : ℕ) (hk : k0 + WT 25 105 ≤ tf) :=
  Composition.machine (okM P tf Pw srcT cntT k1 hk1)
    (iteMachine (flagT P tf k1 hk1) (tailM P tf Pw cr K A srcT cntT k0 hk) (FrontGate.rejM P tf))

theorem okStage_step (Pw : WM 10 56) (capT : ℕ) (σT τT : WState 10 56) (nT : ℕ) (hP : WExec capT Pw σT τT nT)
    (hsT : ∀ i, σT.sh i = 0) (hvT : ∀ r, σT.val r = 0) (hcT : σT.cell = false) (hO : σT.st 0 = [])
    (hkeep : ∀ i : Fin 10, τT.st i.succ = σT.st i.succ) (W : ℕ) (hcap : capT ≤ 2 * W + 2)
    (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (k1 : ℕ) (hk1 : k1 + WT 11 56 ≤ tf)
    (hsI : Function.Injective srcT) (hsL : ∀ i, 2 + NL P ≤ (srcT i).val ∧ (srcT i).val < 2 + NL P + k1)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k1) (hcs : ∀ i, srcT i ≠ cntT)
    (H0 : Fin (NW P tf) → ℕ) (A0 : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H0 A0 k1)
    (hsrc : ∀ i : Fin 10, A0 (srcT i) = σT.st i.succ ∧ H0 (srcT i) = 0)
    (hcnt : A0 cntT = List.replicate W true ∧ H0 cntT = 0) :
    ∃ A1 : Fin (NW P tf) → List Bool,
      Step (okM P tf Pw srcT cntT k1 hk1) ((11 * W + 20) + 1 + (1 + 1 + (2 * (nT + 1 + (1 + 1)) + 2))) H0 A0 H0 A1 ∧
      A1 (flagT P tf k1 hk1) = [decide (τT.val 12 ≠ 0)] ∧ (∀ i, A1 (srcT i) = A0 (srcT i)) ∧
      A1 cntT = List.replicate W true ∧
      (∀ y, (∀ j, sl P tf (shO P tf srcT cntT) k1 hk1 j ≠ y) → A1 y = A0 y) := by
  obtain ⟨τ, eτ, hst, hfl⟩ := okW_run Pw capT (2 * W + 2) hcap σT τT nT hP hsT hvT
  obtain ⟨out, k, hs, hout, -, -, hcntO, -⟩ := wfM_step (okW Pw) W _ (ωO σT) τ eτ (fun _ => rfl) (fun _ => rfl) hcT
  set sl0 := sl P tf (shO P tf srcT cntT) k1 hk1 with hsl0
  have hlow : ∀ j y, shO P tf srcT cntT j = some y → y.val < 2 + NL P + k1 := fun j y h => by
    rcases shO_cases P tf srcT cntT j y h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (hsL _).2
    · exact hcL.2
  have hshI : ∀ i j y, shO P tf srcT cntT i = some y → shO P tf srcT cntT j = some y → i = j := by
    intro i j y hi hj
    have vi : i.val < 72 := i.isLt
    have vj : j.val < 72 := j.isLt
    rcases shO_cases P tf srcT cntT i y hi with ⟨hi1, ei⟩ | ⟨hi1, ei⟩ <;>
      rcases shO_cases P tf srcT cntT j y hj with ⟨hj1, ej⟩ | ⟨hj1, ej⟩ <;>
      have e := ei.symm.trans ej
    · have e2 := congrArg Fin.val (hsI e); simp only at e2; exact Fin.ext (by omega)
    · exact absurd e (hcs _)
    · exact absurd e.symm (hcs _)
    · exact Fin.ext (by omega)
  have hinj : Function.Injective sl0 := sl_inj P tf _ k1 hk1 hshI hlow
  have hA : ∀ j, A0 (sl0 j) = wfIn (ωO σT) W j := by
    intro j
    rw [wfIn_ωO]
    have vj : j.val < 72 := j.isLt
    by_cases h1 : 2 ≤ j.val ∧ j.val ≤ 11
    · rw [hsl0, sl_some P tf _ k1 hk1 j (srcT ⟨j.val - 2, by omega⟩) (by unfold shO; rw [dif_pos h1]),
        (hsrc _).1, if_neg (by omega), if_neg (by omega), dif_pos h1]
      congr 1
      exact Fin.ext (by rw [Fin.val_succ]; show j.val - 2 + 1 = j.val - 1; omega)
    · by_cases h3 : j.val = 71
      · rw [hsl0, sl_some P tf _ k1 hk1 j cntT (by unfold shO; rw [dif_neg h1, if_pos h3]), hcnt.1, if_pos h3]
      · rw [hsl0, sl_none P tf _ k1 hk1 j (by unfold shO; rw [dif_neg h1, if_neg h3]),
          (hPr.1 _ (by rw [rg_val]; omega)).1, if_neg h3]
        by_cases h0 : j.val = 0
        · rw [if_pos h0, hO]
        · rw [if_neg h0, dif_neg h1]
  have hH : ∀ j, H0 (sl0 j) = 0 := by
    intro j
    have vj : j.val < 72 := j.isLt
    by_cases h1 : 2 ≤ j.val ∧ j.val ≤ 11
    · rw [hsl0, sl_some P tf _ k1 hk1 j (srcT ⟨j.val - 2, by omega⟩) (by unfold shO; rw [dif_pos h1])]
      exact (hsrc _).2
    · by_cases h3 : j.val = 71
      · rw [hsl0, sl_some P tf _ k1 hk1 j cntT (by unfold shO; rw [dif_neg h1, if_pos h3])]
        exact hcnt.2
      · rw [hsl0, sl_none P tf _ k1 hk1 j (by unfold shO; rw [dif_neg h1, if_neg h3])]
        exact (hPr.1 _ (by rw [rg_val]; omega)).2
  have d1 := dockAny hs sl0 hinj H0 A0 hH hA
  rw [ExtDecompositionBatch.dockH_existing sl0 H0 (fun _ => 0) hH] at d1
  refine ⟨install sl0 A0 out, d1, ?_, fun i => ?_, ?_, fun y hy => install_other _ _ _ _ hy⟩
  · have e : flagT P tf k1 hk1 = sl0 ⟨12, by show 12 < 72; omega⟩ := by
      rw [hsl0, sl_none P tf _ k1 hk1 _ (by unfold shO; rw [dif_neg (by simp), if_neg (by simp)])]; rfl
    have e2 : (⟨12, by show 12 < 72; omega⟩ : Fin (WT 11 56)) = encL (sTape (nr := 56) (11 : Fin 12)) :=
      Fin.ext rfl
    rw [e, install_slot _ hinj, e2, hout, wenc_A_s, hfl]
  · have e : srcT i = sl0 ⟨i.val + 2, by have := i.isLt; show i.val + 2 < 72; omega⟩ := by
      rw [hsl0, sl_some P tf _ k1 hk1 _ (srcT ⟨(i.val + 2) - 2, by omega⟩)
        (by unfold shO; rw [dif_pos (by simp only; omega)])]
      congr 1
    have e2 : (⟨i.val + 2, by have := i.isLt; show i.val + 2 < 72; omega⟩ : Fin (WT 11 56)) =
        encL (sTape (nr := 56) (Fin.castSucc i.succ)) :=
      Fin.ext (by rw [encL_val]; show i.val + 2 = if (Fin.castSucc i.succ).val = 0 then 0 else (Fin.castSucc i.succ).val + 1
                  simp)
    have e3 : install sl0 A0 out (srcT i) = out ⟨i.val + 2, by have := i.isLt; show i.val + 2 < 72; omega⟩ := by
      rw [e, install_slot _ hinj]
    rw [e3, e2, hout, wenc_A_s, hst, hkeep, (hsrc i).1]
  · have e : cntT = sl0 ⟨71, by show 71 < 72; omega⟩ := by
      rw [hsl0, sl_some P tf _ k1 hk1 _ cntT (by unfold shO; rw [dif_neg (by simp), if_pos rfl])]
    rw [e, install_slot _ hinj]
    exact hcntO

theorem okM_untouched (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (k1 : ℕ) (hk1 : k1 + WT 11 56 ≤ tf)
    (hsL : ∀ i, 2 + NL P ≤ (srcT i).val ∧ (srcT i).val < 2 + NL P + k1)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k1) :
    (∀ y : Fin (NW P tf), 2 + NL P + (k1 + WT 11 56) ≤ y.val → ∀ j, sl P tf (shO P tf srcT cntT) k1 hk1 j ≠ y) ∧
      ∀ i, ∀ j, sl P tf (shO P tf srcT cntT) k1 hk1 j ≠ lp P tf i := by
  have hlow : ∀ j y, shO P tf srcT cntT j = some y → y.val < 2 + NL P + k1 := fun j y h => by
    rcases shO_cases P tf srcT cntT j y h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact (hsL _).2
    · exact hcL.2
  have hshL : ∀ j y, shO P tf srcT cntT j = some y → 2 + NL P ≤ y.val ∨ y.val < 2 := fun j y h => by
    rcases shO_cases P tf srcT cntT j y h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact Or.inl (hsL _).1
    · exact Or.inl hcL.1
  exact ⟨fun y hy => not_slot_of_ge P tf _ k1 hk1 hlow y hy, fun i => not_slot_lp P tf _ k1 hk1 hshL i⟩

/-- **The valid branch**: `OK ≠ 0`; the worker's loop slots end as the loop's entry bank. -/
theorem endGood (Pw : WM 10 56) (capT : ℕ) (σT τT : WState 10 56) (nT : ℕ) (hP : WExec capT Pw σT τT nT)
    (hsT : ∀ i, σT.sh i = 0) (hvT : ∀ r, σT.val r = 0) (hcT : σT.cell = false) (hO : σT.st 0 = [])
    (hkeep : ∀ i : Fin 10, τT.st i.succ = σT.st i.succ) (W : ℕ) (hcap : capT ≤ 2 * W + 2)
    (cr K A q p : ℕ) (a : Fin 6 → ℕ) (s : List Bool)
    (hq : τT.val 54 = q) (hs : τT.st 0 = s) (hsh : τT.sh 0 = s.length) (hL : τT.val 0 = s.length)
    (hp : τT.val 52 = p) (ha : ∀ i : Fin 6, τT.val ⟨24 + i.val, by omega⟩ = a i)
    (hcr : 1 ≤ cr) (h4 : 4 * Ledger.rowBr cr q ≤ q) (hK : 1 ≤ K)
    (hcapW : K * (q + 1) ^ A + 1000 * (q + 7) + 2 * cr + 100 ≤ 2 * W + 2)
    (hpc : p ≤ capOf cr K A q) (hac : ∀ i, a i ≤ capOf cr K A q) (hpW : p ≤ 2 * W + 2)
    (haW : ∀ i, a i ≤ 2 * W + 2) (hsc : s.length ≤ 2 * W + 2) (hok : τT.val 12 ≠ 0)
    (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (k1 : ℕ) (hk1 : k1 + WT 11 56 ≤ tf) (k0 : ℕ)
    (hk : k0 + WT 25 105 ≤ tf) (hk01 : k1 + WT 11 56 ≤ k0)
    (hsI : Function.Injective srcT) (hsL : ∀ i, 2 + NL P ≤ (srcT i).val ∧ (srcT i).val < 2 + NL P + k1)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k1) (hcs : ∀ i, srcT i ≠ cntT)
    (H0 : Fin (NW P tf) → ℕ) (A0 : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H0 A0 k1)
    (hsrc : ∀ i : Fin 10, A0 (srcT i) = σT.st i.succ ∧ H0 (srcT i) = 0)
    (hcnt : A0 cntT = List.replicate W true ∧ H0 cntT = 0) :
    ∃ (H1 : Fin (NW P tf) → ℕ) (A1 : Fin (NW P tf) → List Bool),
      Step (endM P tf Pw cr K A srcT cntT k1 hk1 k0 hk)
        ((11 * W + 20) + 1 + (1 + 1 + (2 * (nT + 1 + (1 + 1)) + 2)) + 1 +
          ((11 * W + 20) + 1 + (1 + 1 + (nT + tailCost cr K A q s.length (2 * W + 2))) + 1 +
            (2 * rOf cr K A q + 4) + 1)) H0 A0 H1 A1 ∧
      (∀ i, H1 (lp P tf i) = bankH P ⟨s, 0, p, a⟩ i) ∧
      (∀ i, A1 (lp P tf i) = bankA P (capOf cr K A q) (rOf cr K A q) (rOf cr K A q + 1) ⟨s, 0, p, a⟩ i) := by
  obtain ⟨A1, s1, fl, srcs, cnt, unt⟩ := okStage_step P tf Pw capT σT τT nT hP hsT hvT hcT hO hkeep W hcap srcT cntT
    k1 hk1 hsI hsL hcL hcs H0 A0 hPr hsrc hcnt
  obtain ⟨nge, nlp⟩ := okM_untouched P tf srcT cntT k1 hk1 hsL hcL
  have hPr1 : PristineH P tf H0 A1 k0 :=
    ⟨fun y hy => by rw [unt y (nge y (by omega))]; exact hPr.1 y (by omega),
     fun i => by rw [unt _ (nlp i)]; exact hPr.2 i⟩
  obtain ⟨H2, A2, s2, hH2, hA2⟩ := tailStage_step P tf Pw capT σT τT nT hP hsT hvT hcT hO W hcap cr K A q p a s hq
    hs hsh hL hp ha hcr h4 hK hcapW hpc hac hpW haW hsc srcT cntT k0 hk hsI
    (fun i => ⟨(hsL i).1, by have := (hsL i).2; omega⟩) ⟨hcL.1, by have := hcL.2; omega⟩ hcs H0 A1 hPr1
    (fun i => ⟨(srcs i).trans (hsrc i).1, (hsrc i).2⟩) ⟨cnt, hcnt.2⟩
  have hb : readTapeBit (A1 (flagT P tf k1 hk1)) (H0 (flagT P tf k1 hk1)) = true := by
    rw [fl, (hPr.1 _ (by unfold flagT; rw [rg_val]; omega)).2]
    simp [hok, readTapeBit]
  exact ⟨H2, A2, Step.seq s1 (iteT _ _ _ hb s2), hH2, hA2⟩

/-- **The rejecting branch**: `OK = 0`; the worker's loop slots end as the rejecting bank. -/
theorem endBad (Pw : WM 10 56) (capT : ℕ) (σT τT : WState 10 56) (nT : ℕ) (hP : WExec capT Pw σT τT nT)
    (hsT : ∀ i, σT.sh i = 0) (hvT : ∀ r, σT.val r = 0) (hcT : σT.cell = false) (hO : σT.st 0 = [])
    (hkeep : ∀ i : Fin 10, τT.st i.succ = σT.st i.succ) (W : ℕ) (hcap : capT ≤ 2 * W + 2) (cr K A : ℕ)
    (hok : τT.val 12 = 0)
    (srcT : Fin 10 → Fin (NW P tf)) (cntT : Fin (NW P tf)) (k1 : ℕ) (hk1 : k1 + WT 11 56 ≤ tf) (k0 : ℕ)
    (hk : k0 + WT 25 105 ≤ tf)
    (hsI : Function.Injective srcT) (hsL : ∀ i, 2 + NL P ≤ (srcT i).val ∧ (srcT i).val < 2 + NL P + k1)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k1) (hcs : ∀ i, srcT i ≠ cntT)
    (H0 : Fin (NW P tf) → ℕ) (A0 : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H0 A0 k1)
    (hsrc : ∀ i : Fin 10, A0 (srcT i) = σT.st i.succ ∧ H0 (srcT i) = 0)
    (hcnt : A0 cntT = List.replicate W true ∧ H0 cntT = 0) :
    ∃ (H1 : Fin (NW P tf) → ℕ) (A1 : Fin (NW P tf) → List Bool),
      Step (endM P tf Pw cr K A srcT cntT k1 hk1 k0 hk)
        ((11 * W + 20) + 1 + (1 + 1 + (2 * (nT + 1 + (1 + 1)) + 2)) + 1 + (3 + 1)) H0 A0 H1 A1 ∧
      (∀ i, H1 (lp P tf i) = bankH P FrontGate.rejKept i) ∧
      (∀ i, A1 (lp P tf i) = bankA P 1 0 0 FrontGate.rejKept i) := by
  obtain ⟨A1, s1, fl, -, -, unt⟩ := okStage_step P tf Pw capT σT τT nT hP hsT hvT hcT hO hkeep W hcap srcT cntT
    k1 hk1 hsI hsL hcL hcs H0 A0 hPr hsrc hcnt
  obtain ⟨-, nlp⟩ := okM_untouched P tf srcT cntT k1 hk1 hsL hcL
  obtain ⟨H2, A2, s2, hH2, hA2, -⟩ := FrontGate.rej_step P tf H0 A1 (fun i => (hPr.2 i).2)
    (fun i => by rw [unt _ (nlp i)]; exact (hPr.2 i).1)
  have hb : readTapeBit (A1 (flagT P tf k1 hk1)) (H0 (flagT P tf k1 hk1)) = false := by
    rw [fl, (hPr.1 _ (by unfold flagT; rw [rg_val]; omega)).2]
    simp [hok, readTapeBit]
  exact ⟨H2, A2, Step.seq s1 (iteF _ _ _ hb s2), hH2, hA2⟩

end Stage

end NearCubicWires.WireExponent3_5.UnionMachine.FrontEnd
