import Proof.Wire_3_5.FinalPass.ThrPtRS1

/-! # S2 (THR per point), part 16: the digits' reports (P3:2596-2629)

**`digBody_spec`**: one digit `D` (both signs, the digit counted): the reports' stream gains `1^{t_D^+} 0 1^{t_D^−} 0`.
**`digLoop_spec`**: the digits `D, …, τ₀ − 1` (counter `111`): after all of them the reports' stream holds
`repWord tp tm` (`tp = [t_0^+, …]`, `tm = [t_0^−, …]`) followed by blanks, its head at the end. Paper quantity: the
digit lists' reports `t_d^±` of row `(g, p)` at the point (row:thr-reported, P3:2615-2629). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.FinalPass.Pop

theorem repWord_snoc : ∀ (L1 L2 : List ℕ) (a b : ℕ), L1.length = L2.length →
    Term.repWord (L1 ++ [a]) (L2 ++ [b]) = Term.repWord L1 L2 ++ ListEval.unary a ++ ListEval.unary b
  | [], [], a, b, _ => by simp [Term.repWord]
  | x :: L1, y :: L2, a, b, h => by
    simp only [List.cons_append, Term.repWord, repWord_snoc L1 L2 a b (by simpa using h), List.append_assoc]
  | [], _ :: _, _, _, h => by simp at h
  | _ :: _, [], _, _, h => by simp at h

theorem repWord_length : ∀ (L1 L2 : List ℕ), L1.length = L2.length →
    (Term.repWord L1 L2).length = (L1.map (· + 1)).sum + (L2.map (· + 1)).sum
  | [], [], _ => rfl
  | x :: L1, y :: L2, h => by
    have := repWord_length L1 L2 (by simpa using h)
    simp only [Term.repWord, List.length_append, ListEval.unary, List.length_replicate, List.length_cons,
      List.length_nil, List.map_cons, List.sum_cons, this]
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

variable (cap : ℕ)

section Digits
variable (σB : WState 16 118) (a τ M : ℕ) (hB : BaseOK σB a τ M)
  (DM DJ : ℕ) (DW : ℕ → ℕ) (row : ℕ → List Bool) (hT5 : σB.st 9 = ListEval.levelWord DM DJ DW row)
  (p r0 A0 : ℕ) (as : List ℕ) (X restR restX : List Bool)
include hB hT5

/-- The report of digit `i`, sign `sgn`. -/
noncomputable def tRep (sgn : Bool) (i : ℕ) : ℕ := ListEval.reportRef DM DJ DW row (popZ sgn i as X)

/-- One digit's step bound. -/
def digCost (p r0 M A0 D DM c5 tp tm : ℕ) : ℕ := 2 * (popCost p r0 M A0 D + repCost DM c5) + 11 * tp + 11 * tm + 40

/-- **One digit**: both signs' reports written, the digit counted. -/
theorem digBody_spec (D : ℕ) (hA0 : ∀ a ∈ as, a ≤ A0) (hMl : as.length = M) (hXl : X.length = 4 * as.length)
    (hrows : ∀ j ≤ DJ, (row j).length = M) (zr0 A Bf : List Bool) (kS : ℕ) (t : TSt)
    (hrw : t.rw = ListEval.unary p ++ ListEval.unary r0 ++ as.flatMap ListEval.unary ++ restR)
    (hx : t.x = frameP X ++ restX) (hz : t.z = zr0 ++ [false]) (hzr : zr0.length = 2 * as.length)
    (hss : t.ss = List.replicate kS false) (hrep : t.rep = A ++ Bf) (hBf : ∀ b ∈ Bf, b = false)
    (hhRw : t.hRw = 0) (hhRep : t.hRep = A.length) (hrH : t.rH = A.length) (hd : t.d = D) (hr : t.r82 = 0)
    (hc1 : popCap p r0 as.length A0 D ≤ cap) (hc2 : ListEval.capOf DM DJ DW row M ≤ cap)
    (hc3 : A.length + tRep DM DJ DW row as X true D + 1 + tRep DM DJ DW row as X false D + 1 ≤ cap)
    (hc4 : D + 1 ≤ cap) :
    ∃ (kS' : ℕ) (Bf' : List Bool), (∀ b ∈ Bf', b = false) ∧
      WExec cap digBody (t.w σB)
        ({ t with
          z := frame (popZ false D as X), ss := List.replicate kS' false,
          rep := A ++ ListEval.unary (tRep DM DJ DW row as X true D) ++
            ListEval.unary (tRep DM DJ DW row as X false D) ++ Bf',
          hRep := A.length + (tRep DM DJ DW row as X true D + 1) + (tRep DM DJ DW row as X false D + 1),
          rH := A.length + (tRep DM DJ DW row as X true D + 1) + (tRep DM DJ DW row as X false D + 1),
          d := D + 1 }.w σB)
        (digCost p r0 as.length A0 D DM (ListEval.capOf DM DJ DW row M) (tRep DM DJ DW row as X true D)
          (tRep DM DJ DW row as X false D)) := by
  obtain ⟨tp, htp⟩ : ∃ tp, tp = tRep DM DJ DW row as X true D := ⟨_, rfl⟩
  obtain ⟨tm, htm⟩ : ∃ tm, tm = tRep DM DJ DW row as X false D := ⟨_, rfl⟩
  rw [← htp, ← htm] at hc3
  rw [← htp, ← htm]
  have hZp : (popZ true D as X).length = M := by rw [popZ_length, hMl]
  have hZm : (popZ false D as X).length = M := by rw [popZ_length, hMl]
  -- the + population and its report
  have e1 := signPop_spec cap true σB a τ M hB p r0 D A0 as X restR restX zr0 t hrw hx hXl hz hzr hA0 hMl hhRw hd hc1
  obtain ⟨t1, ht1⟩ : ∃ t1 : TSt, t1 = { t with z := frame (popZ true D as X) } := ⟨_, rfl⟩
  rw [← ht1] at e1
  have e2 := signRep_spec cap σB a τ M hB DM DJ DW row hT5 (popZ true D as X) hZp kS t1 (by rw [ht1])
    (by rw [ht1]; exact hss) (by rw [ht1]; exact hr) hrows hc2
  rw [hZp, show ListEval.reportRef DM DJ DW row (popZ true D as X) = tp by rw [htp]; rfl] at e2
  obtain ⟨t2, ht2⟩ : ∃ t2 : TSt, t2 = { t1 with
      ss := List.replicate DM false ++ List.replicate (kS - DM) false, r82 := tp } := ⟨_, rfl⟩
  rw [← ht2] at e2
  have e3 := signWr_spec cap σB A Bf tp t2 (by rw [ht2, ht1]; exact hrep) (by rw [ht2, ht1]; exact hhRep)
    (by rw [ht2]) (by rw [ht2, ht1]; exact hrH) (by omega)
  obtain ⟨t3, ht3⟩ : ∃ t3 : TSt, t3 = { t2 with
      rep := A ++ ListEval.unary tp ++ Bf.drop (tp + 1), hRep := A.length + tp + 1, rH := A.length + tp + 1,
      r82 := 0 } := ⟨_, rfl⟩
  rw [← ht3] at e3
  -- the − population and its report
  have e4 := signPop_spec cap false σB a τ M hB p r0 D A0 as X restR restX (frameP (popZ true D as X)) t3
    (by rw [ht3, ht2, ht1]; exact hrw) (by rw [ht3, ht2, ht1]; exact hx) hXl
    (by rw [ht3, ht2, ht1]; exact frame_eq_frameP _) (by rw [fP_length, hZp, hMl]) hA0 hMl
    (by rw [ht3, ht2, ht1]; exact hhRw) (by rw [ht3, ht2, ht1]; exact hd) hc1
  obtain ⟨t4, ht4⟩ : ∃ t4 : TSt, t4 = { t3 with z := frame (popZ false D as X) } := ⟨_, rfl⟩
  rw [← ht4] at e4
  have e5 := signRep_spec cap σB a τ M hB DM DJ DW row hT5 (popZ false D as X) hZm (DM + (kS - DM)) t4
    (by rw [ht4]) (by rw [ht4, ht3, ht2, List.replicate_add]) (by rw [ht4, ht3]) hrows hc2
  rw [hZm, show ListEval.reportRef DM DJ DW row (popZ false D as X) = tm by rw [htm]; rfl] at e5
  obtain ⟨t5, ht5⟩ : ∃ t5 : TSt, t5 = { t4 with
      ss := List.replicate DM false ++ List.replicate (DM + (kS - DM) - DM) false, r82 := tm } := ⟨_, rfl⟩
  rw [← ht5] at e5
  have e6 := signWr_spec cap σB (A ++ ListEval.unary tp) (Bf.drop (tp + 1)) tm t5
    (by rw [ht5, ht4, ht3]) (by rw [ht5, ht4, ht3]; simp [ListEval.unary]; omega) (by rw [ht5])
    (by rw [ht5, ht4, ht3]; simp [ListEval.unary]; omega) (by simp [ListEval.unary]; omega)
  obtain ⟨t6, ht6⟩ : ∃ t6 : TSt, t6 = { t5 with
      rep := A ++ ListEval.unary tp ++ ListEval.unary tm ++ (Bf.drop (tp + 1)).drop (tm + 1),
      hRep := (A ++ ListEval.unary tp).length + tm + 1, rH := (A ++ ListEval.unary tp).length + tm + 1,
      r82 := 0 } := ⟨_, rfl⟩
  rw [← ht6] at e6
  -- the digit counted
  have hd6 : t6.d = D := by rw [ht6, ht5, ht4, ht3, ht2, ht1]; exact hd
  have e7 := WExec.inc (cap := cap) (53 : Fin 118) (t6.w σB) (by rw [tw_val_d, hd6]; omega)
  rw [tw_val_d, tw_setv_d] at e7
  refine ⟨DM + (DM + (kS - DM) - DM), (Bf.drop (tp + 1)).drop (tm + 1),
    fun b hb => hBf b (List.mem_of_mem_drop (List.mem_of_mem_drop hb)),
    WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6 e7))))))
      (tw_eq ?_) ?_⟩
  · rw [ht6, ht5, ht4, ht3, ht2, ht1]
    simp only [List.replicate_add, ListEval.unary, List.length_append, List.length_replicate, List.length_cons,
      List.length_nil]
    obtain ⟨⟩ := t
    simp only at hd hr ⊢
    simp only [TSt.mk.injEq, true_and, and_true]
    exact ⟨by omega, hr.symm, by omega⟩
  · unfold digCost
    omega

end Digits

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
