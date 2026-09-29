import Proof.Wire_3_5.FinalPass.ThrPtRS6

/-! # S2 (THR per point), part 21: the row word's loops

**`coefLoop_spec`**: the coefficients `1^{a_i} 0` erased (counter `114` down, `115` up). **`digWLoop_spec`**: the
digit weights `1 1^{w_d} 0` erased (counter `111` down, `53` up). Paper quantity: none beyond the machine model. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

variable (cap : ℕ) (σB : WState 16 118)

/-- The coefficients' eraser. -/
def coefLoop : TProg := .whr 114 (.seq (.dec 114) (.seq (.inc 115) erW))

theorem coefLoop_spec (A0 : ℕ) (R : List Bool) :
    ∀ (asS : List ℕ) (t : TSt) (e j : ℕ), (∀ x ∈ asS, x ≤ A0) →
      t.rw = List.replicate e false ++ asS.flatMap ListEval.unary ++ R → t.hRw = e → t.rwH = e → t.kS = asS.length →
      t.rS = j → e + (asS.map (· + 1)).sum ≤ cap → j + asS.length ≤ cap →
      WExec cap coefLoop (t.w σB)
        ({ t with
          rw := List.replicate (e + (asS.map (· + 1)).sum) false ++ R, hRw := e + (asS.map (· + 1)).sum,
          rwH := e + (asS.map (· + 1)).sum, kS := 0, rS := j + asS.length }.w σB) (asS.length * (9 * A0 + 30) + 1)
  | [], t, e, j, _, hrw, hh, hr, hk, hs, _, _ => by
    refine WExec.cast cap (WExec.whrF (show (t.w σB).val 114 = 0 by rw [tw_val_kS, hk]; rfl)) (tw_eq ?_) (by simp)
    obtain ⟨⟩ := t
    simp only at hrw hh hr hk hs ⊢
    subst hrw hh hr hk hs
    simp
  | x :: asS, t, e, j, hA, hrw, hh, hr, hk, hs, hc, hj => by
    have hx : x ≤ A0 := hA x (by simp)
    have hsum : ((x :: asS).map (· + 1)).sum = x + 1 + (asS.map (· + 1)).sum := by simp
    rw [hsum] at hc
    simp only [List.length_cons] at hk hj
    have e0 := WExec.dec (cap := cap) (114 : Fin 118) (t.w σB) (by rw [tw_val_kS, hk]; omega)
    rw [tw_val_kS, tw_setv_kS] at e0
    have e1 := WExec.inc (cap := cap) (115 : Fin 118) ({ t with kS := t.kS - 1 }.w σB)
      (by rw [tw_val_rS]; show t.rS < cap; rw [hs]; omega)
    rw [tw_val_rS, tw_setv_rS] at e1
    have e2 := erW_spec cap σB { { t with kS := t.kS - 1 } with rS := t.rS + 1 } e x (asS.flatMap ListEval.unary ++ R)
      (by show t.rw = _; rw [hrw]; simp [List.append_assoc]) hh hr (by omega)
    have ih := coefLoop_spec A0 R asS { { { t with kS := t.kS - 1 } with rS := t.rS + 1 } with
      rw := List.replicate (e + x + 1) false ++ (asS.flatMap ListEval.unary ++ R), hRw := e + x + 1, rwH := e + x + 1 }
      (e + x + 1) (j + 1) (fun z hz => hA z (by simp [hz])) (by simp [List.append_assoc]) rfl rfl
      (by show t.kS - 1 = _; omega) (by show t.rS + 1 = _; omega) (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show (t.w σB).val 114 ≠ 0 by rw [tw_val_kS, hk]; omega)
      (WExec.seq e0 (WExec.seq e1 e2)) ih) (tw_eq ?_) ?_
    · obtain ⟨⟩ := t
      simp only at hh hr hk hs ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons, TSt.mk.injEq, true_and, and_true]
      repeat' constructor
      all_goals first | omega | (congr 2; omega)
    · simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

/-- The digit weights' eraser. -/
def digWLoop : TProg := .whr 111 (.seq (.dec 111) (.seq (.inc 53) (.seq wrW erW)))

theorem digWLoop_spec (A0 : ℕ) (R : List Bool) :
    ∀ (wsS : List ℕ) (t : TSt) (e j : ℕ), (∀ x ∈ wsS, x ≤ A0) →
      t.rw = List.replicate e false ++ Term.digWord wsS ++ R → t.hRw = e → t.rwH = e → t.dRem = wsS.length →
      t.d = j → e + (wsS.map (· + 2)).sum ≤ cap → j + wsS.length ≤ cap →
      WExec cap digWLoop (t.w σB)
        ({ t with
          rw := List.replicate (e + (wsS.map (· + 2)).sum) false ++ R, hRw := e + (wsS.map (· + 2)).sum,
          rwH := e + (wsS.map (· + 2)).sum, dRem := 0, d := j + wsS.length }.w σB) (wsS.length * (9 * A0 + 40) + 1)
  | [], t, e, j, _, hrw, hh, hr, hk, hs, _, _ => by
    refine WExec.cast cap (WExec.whrF (show (t.w σB).val 111 = 0 by rw [tw_val_dRem, hk]; rfl)) (tw_eq ?_) (by simp)
    obtain ⟨⟩ := t
    simp only at hrw hh hr hk hs ⊢
    subst hrw hh hr hk hs
    simp [Term.digWord]
  | w :: wsS, t, e, j, hA, hrw, hh, hr, hk, hs, hc, hj => by
    have hw : w ≤ A0 := hA w (by simp)
    have hsum : ((w :: wsS).map (· + 2)).sum = w + 2 + (wsS.map (· + 2)).sum := by simp
    rw [hsum] at hc
    simp only [List.length_cons] at hk hj
    have e0 := WExec.dec (cap := cap) (111 : Fin 118) (t.w σB) (by rw [tw_val_dRem, hk]; omega)
    rw [tw_val_dRem, tw_setv_dRem] at e0
    have e1 := WExec.inc (cap := cap) (53 : Fin 118) ({ t with dRem := t.dRem - 1 }.w σB)
      (by rw [tw_val_d]; show t.d < cap; rw [hs]; omega)
    rw [tw_val_d, tw_setv_d] at e1
    have e2 := wrW_spec cap σB { { t with dRem := t.dRem - 1 } with d := t.d + 1 } e true
      (ListEval.unary w ++ Term.digWord wsS ++ R) (by show t.rw = _; rw [hrw]; simp [Term.digWord, List.append_assoc])
      hh hr (by omega)
    have e3 := erW_spec cap σB { { { t with dRem := t.dRem - 1 } with d := t.d + 1 } with
      rw := List.replicate (e + 1) false ++ (ListEval.unary w ++ Term.digWord wsS ++ R), hRw := e + 1, rwH := e + 1 }
      (e + 1) w (Term.digWord wsS ++ R) (by simp [List.append_assoc]) rfl rfl (by omega)
    have ih := digWLoop_spec A0 R wsS { { { { t with dRem := t.dRem - 1 } with d := t.d + 1 } with
      rw := List.replicate (e + 1) false ++ (ListEval.unary w ++ Term.digWord wsS ++ R), hRw := e + 1,
      rwH := e + 1 } with
      rw := List.replicate (e + 1 + w + 1) false ++ (Term.digWord wsS ++ R), hRw := e + 1 + w + 1,
      rwH := e + 1 + w + 1 } (e + 1 + w + 1) (j + 1) (fun z hz => hA z (by simp [hz])) (by simp [List.append_assoc])
      rfl rfl (by show t.dRem - 1 = _; omega) (by show t.d + 1 = _; omega) (by omega) (by omega)
    refine WExec.cast cap (WExec.whrT (show (t.w σB).val 111 ≠ 0 by rw [tw_val_dRem, hk]; omega)
      (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3))) ih) (tw_eq ?_) ?_
    · obtain ⟨⟩ := t
      simp only at hh hr hk hs ⊢
      simp only [List.map_cons, List.sum_cons, List.length_cons, TSt.mk.injEq, true_and, and_true]
      repeat' constructor
      all_goals first | omega | (congr 2; omega)
    · simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
