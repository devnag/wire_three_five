import Proof.Wire_3_5.FinalPass.ThrPtRS4

/-! # S2 (THR per point), part 19: erasing the reports

The reports' word `repWord tp tm` is erased in place, word by word (`erRepLoop`, two unary words per digit, the digit
counter `53` counting up while `111` counts down; then `111` restored from `53`), so the reports' stream is blank
again for the next row: **`erRepLoop_spec`**. Paper quantity: none beyond the machine model (loop-safe scratch). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- Close a working-state record equality: split the fields, then arithmetic or list normalization. -/
syntax "tclose" : tactic
macro_rules
  | `(tactic| tclose) => `(tactic| ((simp only [TSt.mk.injEq, true_and, and_true]) <;> (repeat' constructor) <;>
      (first | omega | rfl | (simp only [List.append_assoc, ← List.replicate_add]; done) | (congr 1; omega) |
        (simp [List.append_assoc, ← List.replicate_add]; omega))))

variable (cap : ℕ) (σB : WState 16 118)

/-- Erase one unary word on the reports' stream (head counter `112`). -/
def erRep : TProg := eraseU.liftW (fsU 16) (frU 112 115 114)

theorem erRep_spec (t : TSt) (e n : ℕ) (B : List Bool) (hrep : t.rep = List.replicate e false ++ (ListEval.unary n ++ B))
    (hh : t.hRep = e) (hr : t.rH = e) (hc : e + n + 1 ≤ cap) :
    WExec cap erRep (t.w σB)
      ({ t with rep := List.replicate (e + n + 1) false ++ B, hRep := e + n + 1, rH := e + n + 1 }.w σB)
      (9 * n + 1 + 1 + 7) := by
  have e1 := eraseUL_spec cap 16 112 115 114 (by decide) (by decide) (by decide) (List.replicate e false) B n (t.w σB)
    (by rw [tw_st_rep, hrep]) (by rw [tw_sh_hRep, hh]; simp) (by rw [tw_val_rH, hr]; exact hc)
  unfold ustOut at e1
  rw [tw_sets_rep, tw_seth_hRep, tw_setv_rH, tw_setv_rS, tw_setv_kS] at e1
  refine WExec.cast cap e1 (tw_eq ?_) le_rfl
  simp only [tw_sh_hRep, tw_val_rH, tw_val_rS, tw_val_kS]
  obtain ⟨⟩ := t
  simp only at hh hr ⊢
  tclose

/-- Erase the reports, digit by digit. -/
def erRepLoop : TProg := .whr 111 (.seq (.dec 111) (.seq (.inc 53) (.seq erRep erRep)))

theorem erRepLoop_spec (Bf : List Bool) (A0 : ℕ) :
    ∀ (tp tm : List ℕ) (t : TSt) (e j : ℕ), tp.length = tm.length → (∀ x ∈ tp, x ≤ A0) → (∀ x ∈ tm, x ≤ A0) →
      t.rep = List.replicate e false ++ Term.repWord tp tm ++ Bf → t.hRep = e → t.rH = e →
      t.dRem = tp.length → t.d = j → e + (Term.repWord tp tm).length ≤ cap → j + tp.length ≤ cap →
      WExec cap erRepLoop (t.w σB)
        ({ t with
          rep := List.replicate (e + (Term.repWord tp tm).length) false ++ Bf,
          hRep := e + (Term.repWord tp tm).length, rH := e + (Term.repWord tp tm).length,
          dRem := 0, d := j + tp.length }.w σB) (tp.length * (18 * A0 + 50) + 1)
  | [], [], t, e, j, _, _, _, hrep, hh, hr, hm, hd, _, _ => by
    refine WExec.cast cap (WExec.whrF (show (t.w σB).val 111 = 0 by rw [tw_val_dRem, hm]; rfl)) (tw_eq ?_) (by simp)
    obtain ⟨⟩ := t
    simp only at hrep hh hr hm hd ⊢
    subst hrep hh hr hm hd
    simp [Term.repWord]
  | x :: tp, y :: tm, t, e, j, hl, hx, hy, hrep, hh, hr, hm, hd, hc, hj => by
    have hl' : tp.length = tm.length := by simpa using hl
    have hx0 : x ≤ A0 := hx x (by simp)
    have hy0 : y ≤ A0 := hy y (by simp)
    have hlen : (Term.repWord (x :: tp) (y :: tm)).length = x + 1 + (y + 1) + (Term.repWord tp tm).length := by
      simp [Term.repWord, ListEval.unary]; omega
    have e0 := WExec.dec (cap := cap) (111 : Fin 118) (t.w σB) (by rw [tw_val_dRem, hm]; simp only [List.length_cons] at hj ⊢; omega)
    rw [tw_val_dRem, tw_setv_dRem] at e0
    have e1 := WExec.inc (cap := cap) (53 : Fin 118) ({ t with dRem := t.dRem - 1 }.w σB)
      (by rw [tw_val_d]; show t.d < cap; rw [hd]; simp only [List.length_cons] at hj; omega)
    rw [tw_val_d, tw_setv_d] at e1
    have e2 := erRep_spec cap σB { { t with dRem := t.dRem - 1 } with d := t.d + 1 } e x
      (ListEval.unary y ++ Term.repWord tp tm ++ Bf) (by simp only; rw [hrep]; simp [Term.repWord, List.append_assoc])
      (by simp only; exact hh) (by simp only; exact hr) (by rw [hlen] at hc; omega)
    have e3 := erRep_spec cap σB { { { t with dRem := t.dRem - 1 } with d := t.d + 1 } with
      rep := List.replicate (e + x + 1) false ++ (ListEval.unary y ++ Term.repWord tp tm ++ Bf), hRep := e + x + 1,
      rH := e + x + 1 } (e + x + 1) y (Term.repWord tp tm ++ Bf) (by simp only; simp [List.append_assoc]) rfl rfl
      (by rw [hlen] at hc; omega)
    have ih := erRepLoop_spec Bf A0 tp tm { { { { t with dRem := t.dRem - 1 } with d := t.d + 1 } with
      rep := List.replicate (e + x + 1) false ++ (ListEval.unary y ++ Term.repWord tp tm ++ Bf), hRep := e + x + 1,
      rH := e + x + 1 } with
      rep := List.replicate (e + x + 1 + y + 1) false ++ (Term.repWord tp tm ++ Bf), hRep := e + x + 1 + y + 1,
      rH := e + x + 1 + y + 1 } (e + x + 1 + y + 1) (j + 1) hl' (fun z hz => hx z (by simp [hz]))
      (fun z hz => hy z (by simp [hz])) (by simp only; simp [List.append_assoc]) rfl rfl
      (by simp only; rw [hm]; simp) (by simp only; rw [hd]) (by rw [hlen] at hc; omega) (by simp at hj; omega)
    refine WExec.cast cap (WExec.whrT (show (t.w σB).val 111 ≠ 0 by rw [tw_val_dRem, hm]; simp)
      (WExec.seq e0 (WExec.seq e1 (WExec.seq e2 e3))) ih) (tw_eq ?_) ?_
    · rw [hlen]
      obtain ⟨⟩ := t
      simp only at hd ⊢
      tclose
    · simp only [List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
