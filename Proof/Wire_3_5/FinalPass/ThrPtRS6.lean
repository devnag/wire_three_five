import Proof.Wire_3_5.FinalPass.ThrPtRS5

/-! # S2 (THR per point), part 20: erasing the row word

The row word `rowWord p r₀ as ws = 1^p 0 1^{r₀} 0 (1^{a_i} 0)_i (1 1^{w_d} 0)_d 0` is erased in place by parsing it
(`erW` a unary word, `wrW` one cell; the coefficients' loop on the counter `114` = `M`, restored from `115`; the digit
weights' loop on `111` = `τ₀`, restored from `53`), so RowW finds a blank stream at the next row:
**`coefLoop_spec`**, **`digWLoop_spec`**. Paper quantity: none beyond the machine model (loop-safe scratch). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrPt
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.FinalPass.Tm

/-- `tclose` with the one-cell list normalization. -/
syntax "tclose2" : tactic
macro_rules
  | `(tactic| tclose2) => `(tactic| ((simp only [TSt.mk.injEq, true_and, and_true]) <;> (repeat' constructor) <;>
      (first | omega | rfl | (simp [List.replicate_succ', List.append_assoc]; done) |
        (simp only [List.append_assoc, ← List.replicate_add]; done) | (congr 1; omega))))

variable (cap : ℕ) (σB : WState 16 118)

/-- Erase one unary word on the row word's stream (head counter `116`). -/
def erW : TProg := eraseU.liftW (fsU 13) (frU 116 115 114)

/-- Blank one cell of the row word's stream. -/
def wrW : TProg := (wrStep false).liftW (fsU 13) (frU 116 115 114)

theorem erW_spec (t : TSt) (e n : ℕ) (B : List Bool) (hrw : t.rw = List.replicate e false ++ (ListEval.unary n ++ B))
    (hh : t.hRw = e) (hr : t.rwH = e) (hc : e + n + 1 ≤ cap) :
    WExec cap erW (t.w σB)
      ({ t with rw := List.replicate (e + n + 1) false ++ B, hRw := e + n + 1, rwH := e + n + 1 }.w σB)
      (9 * n + 1 + 1 + 7) := by
  have e1 := eraseUL_spec cap 13 116 115 114 (by decide) (by decide) (by decide) (List.replicate e false) B n (t.w σB)
    (by rw [tw_st_rw, hrw]) (by rw [tw_sh_hRw, hh]; simp) (by rw [tw_val_rwH, hr]; exact hc)
  unfold ustOut at e1
  rw [tw_sets_rw, tw_seth_hRw, tw_setv_rwH, tw_setv_rS, tw_setv_kS] at e1
  refine WExec.cast cap e1 (tw_eq ?_) le_rfl
  simp only [tw_sh_hRw, tw_val_rwH, tw_val_rS, tw_val_kS]
  obtain ⟨⟩ := t
  simp only at hh hr ⊢
  tclose

theorem wrW_spec (t : TSt) (e : ℕ) (b0 : Bool) (B : List Bool) (hrw : t.rw = List.replicate e false ++ (b0 :: B))
    (hh : t.hRw = e) (hr : t.rwH = e) (hc : e + 1 ≤ cap) :
    WExec cap wrW (t.w σB)
      ({ t with rw := List.replicate (e + 1) false ++ B, hRw := e + 1, rwH := e + 1 }.w σB) 7 := by
  have e0 := wrStep_spec cap false (toU (t.w σB) 13 116 115 114) (List.replicate e false) (b0 :: B)
    (by show (t.w σB).st 13 = _; rw [tw_st_rw, hrw]) (by show (t.w σB).sh 13 = _; rw [tw_sh_hRw, hh]; simp)
    (by show (t.w σB).val 116 < cap; rw [tw_val_rwH, hr]; omega)
  have e1 := liftU_upd cap 13 116 115 114 (by decide) (by decide) (by decide) (t.w σB) _ _ _
    ((toU (t.w σB) 13 116 115 114).r) ((toU (t.w σB) 13 116 115 114).k) 7 e0
  unfold ustOut at e1
  rw [tw_sets_rw, tw_seth_hRw, tw_setv_rwH, tw_setv_rS, tw_setv_kS] at e1
  refine WExec.cast cap e1 (tw_eq ?_) le_rfl
  simp only [toU, tw_sh_hRw, tw_val_rwH, tw_val_rS, tw_val_kS]
  obtain ⟨⟩ := t
  simp only at hh hr ⊢
  simp only [TSt.mk.injEq, true_and, and_true]
  refine ⟨by omega, by omega, ?_⟩
  show List.replicate e false ++ false :: B = List.replicate (e + 1) false ++ B
  rw [List.replicate_succ, List.cons_append, cons_rep]

end NearCubicWires.WireExponent3_5.FinalPass.ThrPt
