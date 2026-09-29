import Proof.Wire_3_5.FinalPass.ThrPtRS2

/-! # S2 (THR per point), part 17: all digits (P3:2596-2629)

**`digLoop_spec`**: the digits `D, D + 1, …, τ₀ − 1` (counter `111`), each by `digBody_spec`: the reports' stream ends
as `repWord tp tm` (`tp = [t_0^+, …, t_{τ₀−1}^+]`, `tm` likewise) followed by blanks, its head at the end.
`popCost_mono`: the population builder's bound grows with the digit. Paper quantity: the digit lists' reports of row
`(g, p)` at the point, all digits (row:thr-reported, P3:2615-2629). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

theorem bitDCost_mono_D (A D D' : ℕ) (h : D ≤ D') : bitDCost A D ≤ bitDCost A D' := by
  unfold bitDCost
  have := Nat.mul_le_mul_right (12 * A + 7) h
  omega

theorem popCost_mono (p r0 M A0 D D' : ℕ) (h : D ≤ D') : popCost p r0 M A0 D ≤ popCost p r0 M A0 D' := by
  unfold popCost occCost
  have h1 := bitDCost_mono_D A0 D D' h
  have h2 := Nat.mul_le_mul_left M (show 11 * A0 + 7 + 1 + (bitDCost A0 D + 1 + 90) + 4 ≤
    11 * A0 + 7 + 1 + (bitDCost A0 D' + 1 + 90) + 4 by omega)
  omega

/-- The reports of digits `0 … D − 1`, sign `sgn`. -/
noncomputable def tRepL (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (as : List ℕ) (X : List Bool) (sgn : Bool)
    (D : ℕ) : List ℕ :=
  (List.range D).map (tRep DM DJ DW row as X sgn)

theorem tRepL_succ (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (as : List ℕ) (X : List Bool) (sgn : Bool)
    (D : ℕ) : tRepL DM DJ DW row as X sgn (D + 1) = tRepL DM DJ DW row as X sgn D ++ [tRep DM DJ DW row as X sgn D] := by
  simp [tRepL, List.range_succ]

theorem tRepL_length (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (as : List ℕ) (X : List Bool) (sgn : Bool)
    (D : ℕ) : (tRepL DM DJ DW row as X sgn D).length = D := by
  simp [tRepL]

theorem tRep_le (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (as : List ℕ) (X : List Bool) (sgn : Bool) (i : ℕ) :
    tRep DM DJ DW row as X sgn i ≤ DM := reportRef_le DM DJ DW row _

variable (cap : ℕ)

/-- **All digits**: `digBody` while `DREM ≠ 0`. -/
def digLoop : TProg := .whr 111 (.seq (.dec 111) digBody)

/-- The digits' step bound. -/
def digLoopCost (m p r0 M A0 τ DM c5 : ℕ) : ℕ := m * (digCost p r0 M A0 τ DM c5 DM DM + 4) + 1

theorem repWordL_length (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (as : List ℕ) (X : List Bool) (D : ℕ) :
    (Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D)).length ≤ 2 * D * (DM + 1) := by
  induction D with
  | zero => simp [tRepL, Term.repWord]
  | succ D ih =>
    rw [tRepL_succ, tRepL_succ, repWord_snoc _ _ _ _ (by rw [tRepL_length, tRepL_length])]
    simp only [List.length_append, ListEval.unary, List.length_replicate, List.length_cons, List.length_nil]
    have h1 := tRep_le DM DJ DW row as X true D
    have h2 := tRep_le DM DJ DW row as X false D
    nlinarith [ih, h1, h2]

theorem digLoop_spec (σB : WState 16 118) (a τ M : ℕ) (hB : BaseOK σB a τ M)
    (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (hT5 : σB.st 9 = ListEval.levelWord DM DJ DW row)
    (p r0 A0 : ℕ) (as : List ℕ) (X restR restX : List Bool) (hA0 : ∀ a ∈ as, a ≤ A0) (hMl : as.length = M)
    (hXl : X.length = 4 * as.length) (hrows : ∀ j ≤ DJ, (row j).length = M)
    (hc1 : popCap p r0 as.length A0 τ ≤ cap) (hc2 : ListEval.capOf DM DJ DW row M ≤ cap)
    (hc3 : 2 * τ * (DM + 1) + 2 * (DM + 1) ≤ cap) (hc4 : τ + 1 ≤ cap) :
    ∀ (m D : ℕ) (t : TSt) (zr0 Bf : List Bool) (kS : ℕ), D + m = τ → t.dRem = m → t.d = D →
      t.rw = ListEval.unary p ++ ListEval.unary r0 ++ as.flatMap ListEval.unary ++ restR →
      t.x = frameP X ++ restX → t.z = zr0 ++ [false] → zr0.length = 2 * as.length →
      t.ss = List.replicate kS false →
      t.rep = Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D) ++ Bf →
      (∀ b ∈ Bf, b = false) → t.hRw = 0 →
      t.hRep = (Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D)).length →
      t.rH = (Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D)).length →
      t.r82 = 0 →
      ∃ (zr1 : List Bool) (kS' : ℕ) (Bf' : List Bool), zr1.length = 2 * as.length ∧ (∀ b ∈ Bf', b = false) ∧
        WExec cap digLoop (t.w σB)
          ({ t with
            z := zr1 ++ [false], ss := List.replicate kS' false,
            rep := Term.repWord (tRepL DM DJ DW row as X true τ) (tRepL DM DJ DW row as X false τ) ++ Bf',
            hRep := (Term.repWord (tRepL DM DJ DW row as X true τ) (tRepL DM DJ DW row as X false τ)).length,
            rH := (Term.repWord (tRepL DM DJ DW row as X true τ) (tRepL DM DJ DW row as X false τ)).length,
            d := τ, dRem := 0 }.w σB)
          (digLoopCost m p r0 as.length A0 τ DM (ListEval.capOf DM DJ DW row M)) := by
  intro m
  induction m with
  | zero =>
    intro D t zr0 Bf kS hDm hm hd hrw hx hz hzr hss hrep hBf hhRw hhRep hrH hr
    simp only [Nat.add_zero] at hDm
    subst hDm
    refine ⟨zr0, kS, Bf, hzr, hBf, WExec.cast cap (WExec.whrF (show (t.w σB).val 111 = 0 by rw [tw_val_dRem, hm]))
      (tw_eq ?_) (by unfold digLoopCost; omega)⟩
    obtain ⟨⟩ := t
    simp only at hm hd hz hss hrep hhRep hrH ⊢
    subst hm hd hz hss hrep hhRep hrH
    rfl
  | succ m ih =>
    intro D t zr0 Bf kS hDm hm hd hrw hx hz hzr hss hrep hBf hhRw hhRep hrH hr
    have hDle : D + 1 ≤ τ := by omega
    have hRl := repWordL_length DM DJ DW row as X D
    have htp := tRep_le DM DJ DW row as X true D
    have htm := tRep_le DM DJ DW row as X false D
    have e0 := WExec.dec (cap := cap) (111 : Fin 118) (t.w σB) (by rw [tw_val_dRem, hm]; omega)
    rw [tw_val_dRem, tw_setv_dRem] at e0
    obtain ⟨kS1, Bf1, hBf1, e1⟩ := digBody_spec cap σB a τ M hB DM DJ DW row hT5 p r0 A0 as X restR restX D hA0 hMl
      hXl hrows zr0 (Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D)) Bf kS
      { t with dRem := t.dRem - 1 } hrw hx hz hzr hss hrep hBf hhRw hhRep hrH hd hr
      (le_trans (by unfold popCap; omega) hc1) hc2 (by
        have : 2 * D * (DM + 1) + 2 * (DM + 1) ≤ 2 * τ * (DM + 1) + 2 * (DM + 1) := by
          have := Nat.mul_le_mul_right (DM + 1) (show 2 * D ≤ 2 * τ by omega); omega
        omega) (by omega)
    obtain ⟨t2, ht2⟩ : ∃ t2 : TSt, t2 = { { t with dRem := t.dRem - 1 } with
        z := frame (popZ false D as X), ss := List.replicate kS1 false,
        rep := Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D) ++
          ListEval.unary (tRep DM DJ DW row as X true D) ++ ListEval.unary (tRep DM DJ DW row as X false D) ++ Bf1,
        hRep := (Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D)).length +
          (tRep DM DJ DW row as X true D + 1) + (tRep DM DJ DW row as X false D + 1),
        rH := (Term.repWord (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D)).length +
          (tRep DM DJ DW row as X true D + 1) + (tRep DM DJ DW row as X false D + 1),
        d := D + 1 } := ⟨_, rfl⟩
    rw [← ht2] at e1
    have hsnoc := repWord_snoc (tRepL DM DJ DW row as X true D) (tRepL DM DJ DW row as X false D)
      (tRep DM DJ DW row as X true D) (tRep DM DJ DW row as X false D) (by rw [tRepL_length, tRepL_length])
    obtain ⟨zr1, kS', Bf', hzr1, hBf', e2⟩ := ih (D + 1) t2 (frameP (popZ false D as X)) Bf1 kS1 (by omega)
      (by rw [ht2]; simp only; omega) (by rw [ht2]) (by rw [ht2]; exact hrw) (by rw [ht2]; exact hx)
      (by rw [ht2]; exact frame_eq_frameP _) (by rw [fP_length, popZ_length]) (by rw [ht2])
      (by rw [ht2]; simp only; rw [tRepL_succ, tRepL_succ, hsnoc])
      hBf1 (by rw [ht2]; exact hhRw)
      (by rw [ht2]; simp only; rw [tRepL_succ, tRepL_succ, hsnoc]; simp [ListEval.unary]; omega)
      (by rw [ht2]; simp only; rw [tRepL_succ, tRepL_succ, hsnoc]; simp [ListEval.unary]; omega)
      (by rw [ht2]; exact hr)
    refine ⟨zr1, kS', Bf', hzr1, hBf', WExec.cast cap (WExec.whrT (show (t.w σB).val 111 ≠ 0 by
      rw [tw_val_dRem, hm]; omega) (WExec.seq e0 e1) e2) (tw_eq ?_) ?_⟩
    · rw [ht2]
    · unfold digLoopCost digCost
      have hp := popCost_mono p r0 as.length A0 D τ (by omega)
      rw [Nat.add_mul, Nat.one_mul]
      unfold digLoopCost at *
      omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
