import Proof.Wire_3_5.FinalPass.DigsLay

/-! # `DigsW`'s body, part 2: a payload's header and the selected child's index (P3:2543-2551)

A payload is `frame (natWord |supp| ++ natWord |children| ++ children.flatMap exactWord)` (`EqRead.payOf_eq`).
`navHeadW` steps onto the content, reads `S = |supp|` into `R 15` and `m = |children|` into `R 16`, divides the
selection register `R 17 = g` by `m` (`R 17 := g / m`, `R 18 := g mod m`, the child index `g_i` of `EqRead.sel_digit`)
and clears `m`. The state algebra: `Zs` facts through `at2`/`setv`, and `wst_eq` (register-by-register equality of
two states built from the same state by `setv`/`seth`/`sets`). Main declarations: `Zs_at2`, `Zs_setv`, `Zs_sub`,
**`navHead_spec`**. Paper quantities: `|supp_i|`, `|children_i|` and the child index `g_i`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.DigsBody
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore
open NearCubicWires.WireExponent3_5.FinalPass.ThrRead NearCubicWires.WireExponent3_5.FinalPass.ThrArith
open NearCubicWires.WireExponent3_5.FinalPass.Digs
open NearCubicWires.RepairRepresentation (natWord intWord)

/-- Two states built from one state by `setv`/`seth`/`sets` (and `at2`, `outAt`), compared field by field. -/
macro "wst_eq" : tactic => `(tactic| (apply WState.eq <;> (try funext _) <;>
  simp only [at2, outAt, WState.setv_val, WState.seth_val, WState.sets_val, WState.setv_sh, WState.seth_sh,
    WState.sets_sh, WState.setv_st, WState.seth_st, WState.sets_st, WState.setv_cell, WState.seth_cell,
    WState.sets_cell, Function.update_apply] <;> (try split_ifs) <;> simp_all))

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

@[simp] theorem dmE0 : dmE R 0 = R 17 := rfl
@[simp] theorem dmE1 : dmE R 1 = R 16 := rfl
@[simp] theorem dmE2 : dmE R 2 = R 21 := rfl
@[simp] theorem dmE3 : dmE R 3 = R 18 := rfl
@[simp] theorem dmE4 : dmE R 4 = R 22 := rfl
@[simp] theorem dmE5 : dmE R 5 = R 39 := rfl

theorem Zs_sub (τ : WState ns nr) (l l' : List (Fin digsK)) (h : ∀ k ∈ l', k ∈ l) (hz : Zs R τ l) : Zs R τ l' :=
  fun k hk => hz k (h k hk)

theorem Zs_at2 (τ : WState ns nr) (E : Fin (ns + 1)) (j : ℕ) (l : List (Fin digsK)) (h : (14 : Fin digsK) ∉ l)
    (hz : Zs R τ l) : Zs R (at2 τ E (R 14) j) l := fun k hk => by
  have hk' : k ≠ 14 := fun e => h (e ▸ hk)
  rw [at2_val_ne _ _ _ _ _ (R.injective.ne hk')]; exact hz k hk

theorem Zs_setv (τ : WState ns nr) (r : Fin digsK) (v : ℕ) (l : List (Fin digsK)) (h : r ∉ l) (hz : Zs R τ l) :
    Zs R (τ.setv (R r) v) l := fun k hk => by
  have hk' : k ≠ r := fun e => h (e ▸ hk)
  simp [Function.update_apply, R.injective.ne hk', hz k hk]

/-- The header's zero registers. -/
def headL : List (Fin digsK) := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 21, 22, 39]

/-- The header: `S` into `R 15`, `m` into `R 16`, `R 17 := g / m`, `R 18 := g mod m`, `m` cleared. -/
def navHeadW (E : Fin (ns + 1)) : WM ns nr :=
  .seq (.fwd E) (.seq (natW2W E (R 14) (Rg R)) (.seq (WM.move (R 5) (R 15)) (.seq (natW2W E (R 14) (Rg R))
    (.seq (WM.move (R 5) (R 16)) (.seq (divmodW (dmE R)) (.seq (WM.move (R 21) (R 17)) (WM.clear (R 16))))))))

/-- The header's step bound. -/
def headCost (S m g : ℕ) : ℕ :=
  1 + 1 + (natCost S + 1 + (7 * S + 1 + 1 + (natCost m + 1 + (7 * m + 1 + 1 +
    ((18 * m + 3 + 1 + (g * (7 * m + 17) + 1 + 1 + (3 * m + 1))) + 1 + (7 * (g / m) + 1 + 1 + (3 * m + 1)))))))

theorem navHead_spec (E : Fin (ns + 1)) (S m g : ℕ) (c rest : List Bool) (σ : WState ns nr)
    (hst : σ.st E = frame c) (hs : σ.sh E = 0) (hc : c = natWord S ++ (natWord m ++ rest))
    (hz : Zs R σ headL) (hg : σ.val (R 17) = g) (hm : 1 ≤ m)
    (hcS : (natWord S).length + (natWord m).length ≤ cap) (hS : 2 * S + 2 ≤ cap) (hM : 2 * m + 2 ≤ cap)
    (hgc : g ≤ cap) :
    WExec cap (navHeadW R E) σ
      (at2 (((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 18) (g % m)) E (R 14)
        ((natWord S).length + (natWord m).length)) (headCost S m g) := by
  have hPc := Rg_ne_Pc R
  have h5 := hz 5 (by decide)
  have h14 := hz 14 (by decide)
  have h15 := hz 15 (by decide)
  have h16 := hz 16 (by decide)
  have h18 := hz 18 (by decide)
  have h21 := hz 21 (by decide)
  have h22 := hz 22 (by decide)
  have h39 := hz 39 (by decide)
  have hdm := Nat.div_le_self g m
  -- 1. onto the content
  have d1 := WExec.fwd (cap := cap) E σ
  have e1 : σ.seth E (σ.sh E + 1) = at2 σ E (R 14) 0 := by
    rw [hs]; clear d1 hz; wst_eq
  rw [e1] at d1
  -- 2. |supp|
  have d2 := natW2_spec cap E (R 14) (Rg R) hPc S c (natWord m ++ rest) 0 (at2 σ E (R 14) 0) (by simp [hst])
    (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _) (by simp [hc])
    (core_zero R _ (Zs_at2 R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz))) (by omega) hS
  have e2 : at2 ((at2 σ E (R 14) 0).setv (Rg R 1) S) E (R 14) (0 + (natWord S).length) =
      at2 (σ.setv (R 5) S) E (R 14) (natWord S).length := by
    clear d1 d2 hz; wst_eq
  rw [e2] at d2
  have d3 := wmove_spec cap (R 5) (R 15) (R.injective.ne (by decide)) S (at2 (σ.setv (R 5) S) E (R 14)
    (natWord S).length) (by simp [at2]) (by simp [at2]; omega) (by simp [at2, h15]; omega)
  have e3 : ((at2 (σ.setv (R 5) S) E (R 14) (natWord S).length).setv (R 5) 0).setv (R 15)
      ((at2 (σ.setv (R 5) S) E (R 14) (natWord S).length).val (R 15) +
        (at2 (σ.setv (R 5) S) E (R 14) (natWord S).length).val (R 5)) =
      at2 (σ.setv (R 15) S) E (R 14) (natWord S).length := by
    clear d1 d2 d3 hz; wst_eq
  rw [e3] at d3
  -- 3. |children|
  have d4 := natW2_spec cap E (R 14) (Rg R) hPc m c rest (natWord S).length
    (at2 (σ.setv (R 15) S) E (R 14) (natWord S).length) (by simp [hst]) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _)
    (by rw [hc, List.drop_left])
    (core_zero R _ (Zs_at2 R _ _ _ _ (by decide) (Zs_setv R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz))))
    (by omega) hM
  have e4 : at2 ((at2 (σ.setv (R 15) S) E (R 14) (natWord S).length).setv (Rg R 1) m) E (R 14)
      ((natWord S).length + (natWord m).length) =
      at2 ((σ.setv (R 15) S).setv (R 5) m) E (R 14) ((natWord S).length + (natWord m).length) := by
    clear d1 d2 d3 d4 hz; wst_eq
  rw [e4] at d4
  have d5 := wmove_spec cap (R 5) (R 16) (R.injective.ne (by decide)) m
    (at2 ((σ.setv (R 15) S).setv (R 5) m) E (R 14) ((natWord S).length + (natWord m).length)) (by simp [at2])
    (by simp [at2]; omega) (by simp [at2, h16]; omega)
  have e5 : ((at2 ((σ.setv (R 15) S).setv (R 5) m) E (R 14) ((natWord S).length + (natWord m).length)).setv (R 5)
      0).setv (R 16) ((at2 ((σ.setv (R 15) S).setv (R 5) m) E (R 14)
        ((natWord S).length + (natWord m).length)).val (R 16) + (at2 ((σ.setv (R 15) S).setv (R 5) m) E (R 14)
        ((natWord S).length + (natWord m).length)).val (R 5)) =
      at2 ((σ.setv (R 15) S).setv (R 16) m) E (R 14) ((natWord S).length + (natWord m).length) := by
    clear d1 d2 d3 d4 d5 hz; wst_eq
  rw [e5] at d5
  -- 4. g / m, g mod m
  have d6 := divmod_spec cap (dmE R) m g hm (by omega) hgc
    (at2 ((σ.setv (R 15) S).setv (R 16) m) E (R 14) ((natWord S).length + (natWord m).length))
    (by simp [at2, hg]) (by simp [at2]) (by simp [at2, h21]) (by simp [at2, h18]) (by simp [at2, h22])
    (by simp [at2, h39])
  simp only [dmE0, dmE2, dmE3] at d6
  have d7 := wmove_spec cap (R 21) (R 17) (R.injective.ne (by decide)) (g / m)
    ((((at2 ((σ.setv (R 15) S).setv (R 16) m) E (R 14) ((natWord S).length + (natWord m).length)).setv (R 17)
      0).setv (R 18) (g % m)).setv (R 21) (g / m)) (by simp) (by simp; omega) (by simp; omega)
  have d8 := wclear_spec cap (R 16) m
    (((((((at2 ((σ.setv (R 15) S).setv (R 16) m) E (R 14) ((natWord S).length + (natWord m).length)).setv (R 17)
      0).setv (R 18) (g % m)).setv (R 21) (g / m)).setv (R 21) 0).setv (R 17)
      (((((at2 ((σ.setv (R 15) S).setv (R 16) m) E (R 14) ((natWord S).length + (natWord m).length)).setv (R 17)
      0).setv (R 18) (g % m)).setv (R 21) (g / m)).val (R 17) +
      ((((at2 ((σ.setv (R 15) S).setv (R 16) m) E (R 14) ((natWord S).length + (natWord m).length)).setv (R 17)
      0).setv (R 18) (g % m)).setv (R 21) (g / m)).val (R 21)))) (by simp [at2]) (by simp [at2]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5
    (WExec.seq d6 (WExec.seq d7 d8))))))) ?_ (by unfold headCost; omega)
  clear d1 d2 d3 d4 d5 d6 d7 d8 hz
  wst_eq

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
