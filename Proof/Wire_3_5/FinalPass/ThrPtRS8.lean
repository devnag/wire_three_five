import Proof.Wire_3_5.FinalPass.ThrPtRS7

/-! # S2 (THR per point), part 22: both erasers, whole

**`erRepAll_spec`**: the reports' word erased, the digits' counter restored, the stream rewound.
**`eraseRow_spec`**: the row word `rowWord p r₀ as ws` erased (the two leading unary words, the coefficients, the
digit weights, the closing `0`), the counters restored, the stream rewound. Both streams end blank (every cell `false`).
Paper quantity: none beyond the machine model (loop-safe scratch). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ) (σB : WState 16 118)

theorem kRestore_spec (t : TSt) (n : ℕ) (hs : t.rS = n) (hk : t.kS = 0) (hc : n ≤ cap) :
    WExec cap (WM.move 115 114) (t.w σB) ({ t with rS := 0, kS := n }.w σB) (7 * n + 1) := by
  have e := wmove_spec cap (115 : Fin 118) 114 (by decide) n (t.w σB) (by rw [tw_val_rS, hs])
    (by rw [tw_val_rS, hs]; exact hc) (by rw [tw_val_kS, tw_val_rS, hk, hs]; omega)
  rw [tw_val_rS, tw_setv_rS, tw_val_kS, tw_setv_kS] at e
  refine WExec.cast cap e (tw_eq ?_) le_rfl
  simp only [hk, hs, Nat.zero_add]

theorem rewRw_spec (t : TSt) (h : t.rwH = t.hRw) (hc : t.rwH ≤ cap) :
    WExec cap (WM.rewind 13 116) (t.w σB) ({ t with rwH := 0, hRw := 0 }.w σB) (5 * t.rwH + 1) := by
  have e := wrewind_spec cap (13 : Fin 17) (116 : Fin 118) t.rwH (t.w σB) (by rw [tw_val_rwH])
    (by rw [tw_val_rwH]; exact hc)
  rw [tw_setv_rwH, tw_sh_hRw, tw_seth_hRw] at e
  refine WExec.cast cap e (tw_eq ?_) le_rfl
  simp only [h, Nat.sub_self]

/-- **The reports erased**: the words, the digits' counter restored, the stream rewound. -/
def erRepAll : TProg := .seq erRepLoop (.seq (WM.move 53 111) (WM.rewind 16 112))

theorem erRepAll_spec (A0 : ℕ) (tp tm : List ℕ) (Bf : List Bool) (t : TSt) (hl : tp.length = tm.length)
    (hx : ∀ x ∈ tp, x ≤ A0) (hy : ∀ x ∈ tm, x ≤ A0) (hrep : t.rep = Term.repWord tp tm ++ Bf) (hh : t.hRep = 0)
    (hr : t.rH = 0) (hm : t.dRem = tp.length) (hd : t.d = 0) (hc : (Term.repWord tp tm).length + tp.length ≤ cap) :
    WExec cap erRepAll (t.w σB)
      ({ t with rep := List.replicate (Term.repWord tp tm).length false ++ Bf }.w σB)
      (tp.length * (18 * A0 + 50) + 1 + 1 + ((7 * tp.length + 1) + 1 + (5 * (Term.repWord tp tm).length + 1))) := by
  have e1 := erRepLoop_spec cap σB Bf A0 tp tm t 0 0 hl hx hy (by rw [hrep]; simp) hh hr hm hd (by omega) (by omega)
  simp only [Nat.zero_add] at e1
  have e2 := dRestore_spec cap σB { t with
      rep := List.replicate (Term.repWord tp tm).length false ++ Bf, hRep := (Term.repWord tp tm).length,
      rH := (Term.repWord tp tm).length, dRem := 0, d := tp.length } tp.length rfl rfl (by omega)
  have e3 := rewRep_spec cap σB { { t with
      rep := List.replicate (Term.repWord tp tm).length false ++ Bf, hRep := (Term.repWord tp tm).length,
      rH := (Term.repWord tp tm).length, dRem := 0, d := tp.length } with d := 0, dRem := tp.length } rfl
      (by simp only; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 e3)) (tw_eq ?_) le_rfl
  obtain ⟨⟩ := t
  simp only at hh hr hm hd ⊢
  simp only [TSt.mk.injEq, true_and, and_true]
  repeat' constructor
  all_goals omega

/-- **The row word erased**. -/
def eraseRow : TProg :=
  .seq erW (.seq erW (.seq coefLoop (.seq (WM.move 115 114) (.seq digWLoop (.seq (WM.move 53 111)
    (.seq wrW (WM.rewind 13 116)))))))

/-- The row eraser's step bound. -/
def eraseRowCost (p r0 M τ A0 len : ℕ) : ℕ :=
  (9 * p + 9) + 1 + ((9 * r0 + 9) + 1 + ((M * (9 * A0 + 30) + 1) + 1 + ((7 * M + 1) + 1 + ((τ * (9 * A0 + 40) + 1) + 1 +
    ((7 * τ + 1) + 1 + (7 + 1 + (5 * len + 1)))))))

theorem rowWord_len (p r0 : ℕ) (as ws : List ℕ) : (Term.rowWord p r0 as ws).length =
    p + 1 + (r0 + 1) + (as.map (· + 1)).sum + (ws.map (· + 2)).sum + 1 := by
  have h1 : ∀ l : List ℕ, (l.flatMap ListEval.unary).length = (l.map (· + 1)).sum := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih => simp [List.flatMap_cons, ListEval.unary, ih]; omega
  have h2 : ∀ l : List ℕ, (Term.digWord l).length = (l.map (· + 2)).sum := by
    intro l; induction l with
    | nil => rfl
    | cons x l ih => simp [Term.digWord, List.flatMap_cons, ListEval.unary] at ih ⊢; omega
  simp only [Term.rowWord, List.length_append, h1, h2, ListEval.unary, List.length_replicate, List.length_cons,
    List.length_nil]

theorem eraseRow_spec (A0 p r0 : ℕ) (as ws : List ℕ) (R : List Bool) (t : TSt) (hA : ∀ x ∈ as, x ≤ A0)
    (hW : ∀ x ∈ ws, x ≤ A0) (hrw : t.rw = Term.rowWord p r0 as ws ++ R) (hh : t.hRw = 0) (hr : t.rwH = 0)
    (hk : t.kS = as.length) (hs : t.rS = 0) (hm : t.dRem = ws.length) (hd : t.d = 0)
    (hc : (Term.rowWord p r0 as ws).length + as.length + ws.length ≤ cap) :
    WExec cap eraseRow (t.w σB)
      ({ t with rw := List.replicate (Term.rowWord p r0 as ws).length false ++ R }.w σB)
      (eraseRowCost p r0 as.length ws.length A0 (Term.rowWord p r0 as ws).length) := by
  have hL := rowWord_len p r0 as ws
  -- 1, 2: the leading unary words
  have e1 := erW_spec cap σB t 0 p (ListEval.unary r0 ++ as.flatMap ListEval.unary ++ Term.digWord ws ++ [false] ++ R)
    (by rw [hrw]; simp [Term.rowWord, List.append_assoc]) hh hr (by omega)
  have e2 := erW_spec cap σB { t with
      rw := List.replicate (0 + p + 1) false ++ (ListEval.unary r0 ++ as.flatMap ListEval.unary ++ Term.digWord ws ++
        [false] ++ R), hRw := 0 + p + 1, rwH := 0 + p + 1 } (0 + p + 1) r0
    (as.flatMap ListEval.unary ++ Term.digWord ws ++ [false] ++ R) (by simp [List.append_assoc]) rfl rfl (by omega)
  -- 3, 4: the coefficients
  have e3 := coefLoop_spec cap σB A0 (Term.digWord ws ++ [false] ++ R) as { { t with
      rw := List.replicate (0 + p + 1) false ++ (ListEval.unary r0 ++ as.flatMap ListEval.unary ++ Term.digWord ws ++
        [false] ++ R), hRw := 0 + p + 1, rwH := 0 + p + 1 } with
      rw := List.replicate (0 + p + 1 + r0 + 1) false ++ (as.flatMap ListEval.unary ++ Term.digWord ws ++ [false] ++ R),
      hRw := 0 + p + 1 + r0 + 1, rwH := 0 + p + 1 + r0 + 1 } (0 + p + 1 + r0 + 1) 0 hA (by simp [List.append_assoc])
    rfl rfl (by simp only; exact hk) (by simp only; exact hs) (by omega) (by omega)
  obtain ⟨t3, ht3⟩ : ∃ t3 : TSt, t3 = { { { t with
      rw := List.replicate (0 + p + 1) false ++ (ListEval.unary r0 ++ as.flatMap ListEval.unary ++ Term.digWord ws ++
        [false] ++ R), hRw := 0 + p + 1, rwH := 0 + p + 1 } with
      rw := List.replicate (0 + p + 1 + r0 + 1) false ++ (as.flatMap ListEval.unary ++ Term.digWord ws ++ [false] ++ R),
      hRw := 0 + p + 1 + r0 + 1, rwH := 0 + p + 1 + r0 + 1 } with
      rw := List.replicate (0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum) false ++ (Term.digWord ws ++ [false] ++ R),
      hRw := 0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum, rwH := 0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum, kS := 0,
      rS := 0 + as.length } := ⟨_, rfl⟩
  rw [← ht3] at e3
  have e4 := kRestore_spec cap σB t3 as.length (by rw [ht3]; simp) (by rw [ht3]) (by omega)
  -- 5, 6: the digit weights
  have e5 := digWLoop_spec cap σB A0 ([false] ++ R) ws { t3 with rS := 0, kS := as.length }
    (0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum) 0 hW (by rw [ht3]; simp [List.append_assoc]) (by rw [ht3])
    (by rw [ht3]) (by rw [ht3]; exact hm) (by rw [ht3]; exact hd) (by omega) (by omega)
  obtain ⟨t5, ht5⟩ : ∃ t5 : TSt, t5 = { { t3 with rS := 0, kS := as.length } with
      rw := List.replicate (0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum + (ws.map (· + 2)).sum) false ++ ([false] ++ R),
      hRw := 0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum + (ws.map (· + 2)).sum,
      rwH := 0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum + (ws.map (· + 2)).sum, dRem := 0, d := 0 + ws.length } :=
    ⟨_, rfl⟩
  rw [← ht5] at e5
  have e6 := dRestore_spec cap σB t5 ws.length (by rw [ht5]; simp) (by rw [ht5]) (by omega)
  -- 7, 8: the closing cell, the rewind
  have e7 := wrW_spec cap σB { t5 with d := 0, dRem := ws.length }
    (0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum + (ws.map (· + 2)).sum) false R (by rw [ht5]; simp) (by rw [ht5])
    (by rw [ht5]) (by omega)
  have e8 := rewRw_spec cap σB { { t5 with d := 0, dRem := ws.length } with
      rw := List.replicate (0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum + (ws.map (· + 2)).sum + 1) false ++ R,
      hRw := 0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum + (ws.map (· + 2)).sum + 1,
      rwH := 0 + p + 1 + r0 + 1 + (as.map (· + 1)).sum + (ws.map (· + 2)).sum + 1 } rfl (by simp only; omega)
  refine WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 (WExec.seq e6
    (WExec.seq e7 e8))))))) (tw_eq ?_) ?_
  · rw [ht5, ht3]
    obtain ⟨⟩ := t
    simp only at hh hr hk hs hm hd ⊢
    simp only [TSt.mk.injEq, true_and, and_true]
    repeat' constructor
    all_goals first | omega | (congr 2; omega)
  · simp only
    unfold eraseRowCost
    rw [hL]
    omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
