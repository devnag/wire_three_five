import Proof.Wire_3_5.FinalPass.DigsDig4

/-! # `DigsW`'s body, part 8: one circuit's term of the stack base, as a circuit body

`cBodyBW` = to the selected child (`navW`), `R 20 := S + 1`, the child's integers (`bIntsW`: weights, then the
target), back to the payload's start, `S` cleared. From `R 23 = x`, `R 24 = p − x` it leaves `bfold p x ys` (the
residue of `x + Σ_{z ∈ ys} |z|`). Main declarations: `cBCost`, **`cBodyB_spec`**. Paper quantity: circuit `i`'s term
`‖child_i‖` of the stack base, modulo `p`. -/

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

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- One circuit's term of the stack base. -/
def cBodyBW (E : Fin (ns + 1)) : WM ns nr :=
  .seq (navW R E) (.seq (Hash4.wcopyR (R 15) (R 20) (R 39)) (.seq (.inc (R 20)) (.seq (bIntsW R E)
    (.seq (rew2W E (R 14)) (WM.clear (R 15))))))

/-- One circuit's step bound for the base. -/
def cBCost (S m g nz Lm p J : ℕ) : ℕ :=
  navCost S m g nz Lm + 1 + (18 * S + 3 + 1 + (3 + 1 + ((S + 1) * (modCost2 Lm p + 1 + (p * (7 * p + 12) + 1) + 4) +
    1 + 1 + ((7 * J + 3) + 1 + (3 * S + 1)))))

/-- A base circuit's zero registers. -/
def cbL : List (Fin digsK) := [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 39, 40]

theorem cBodyB_spec (E : Fin (ns + 1)) (S m g : ℕ) (zs ys : List ℤ) (c rest : List Bool) (p x U : ℕ)
    (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 0)
    (hc : c = natWord S ++ (natWord m ++ (zs.flatMap intWord ++ (ys.flatMap intWord ++ rest))))
    (hzs : zs.length = g % m * (S + 1)) (hys : ys.length = S + 1) (hm : 1 ≤ m) (hp : 1 ≤ p) (hx : x < p)
    (hg : σ.val (R 17) = g) (h23 : σ.val (R 23) = x) (h24 : σ.val (R 24) = p - x) (hP : σ.val (R 2) = p)
    (hz : Zs R σ cbL) (hcU : c.length ≤ U) (hmU : m ≤ U) (hgU : g ≤ U) (hpU : p ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (cBodyBW R E) σ
      (((σ.setv (R 17) (g / m)).setv (R 23) (bfold p x ys)).setv (R 24) (p - bfold p x ys))
      (cBCost S m g zs.length c.length p ((natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
        (ys.flatMap intWord).length)) := by
  have hpos : 0 < p := by omega
  have hlen : c.length = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
      (ys.flatMap intWord).length + rest.length := by rw [hc]; simp only [List.length_append]; ring
  have hzl := fm_len_ge zs
  have hyl := fm_len_ge ys
  have h20 := hz 20 (by decide)
  have h39 := hz 39 (by decide)
  obtain ⟨J1, hJ1⟩ : ∃ J, J = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length := ⟨_, rfl⟩
  have d1 := nav_spec cap R E S m g zs c.length (fun z hz' => le_trans (nbl_le_fm zs z hz') (by omega)) c
    (ys.flatMap intWord ++ rest) σ hst hs hc hzs (Zs_sub R _ _ _ (by decide) hz) hg hm (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [← hJ1] at d1
  have d2 := Hash4.wcopyR_spec cap (R 15) (R 20) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1)
    (by simp [at2, h20]) (by simp [at2, h39]) (by simp [at2]; omega)
  rw [show (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).val (R 15) = S by simp [at2]] at d2
  have d3 := WExec.inc (cap := cap) (R 20) ((at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).setv (R 20) S)
    (by simp; omega)
  have e3 : ((at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).setv (R 20) S).setv (R 20)
      (((at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).setv (R 20) S).val (R 20) + 1) =
      bSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E p J1 ys.length x := by
    unfold bSt; clear d1 d2; rw [hys]
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y1 : y = R 20
      · rw [y1]; simp_all [at2, Function.update_apply]
      by_cases y2 : y = R 23
      · rw [y2]; simp_all [at2, Function.update_apply]
      by_cases y3 : y = R 24
      · rw [y3]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e3] at d3
  have d4 := bInts_spec cap R E ys c.length (fun z hz' => le_trans (nbl_le_fm ys z hz') (by omega)) c rest J1 p x hp
    (by omega) hx ((σ.setv (R 15) S).setv (R 17) (g / m)) (by simp [hst])
    (by rw [hc, hJ1, ← List.append_assoc, ← List.append_assoc, List.drop_left' (by simp; ring)])
    (by simp [hP]) (Zs_setv R _ _ _ _ (by decide) (Zs_setv R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz)))
    (by omega) (by omega)
  have d5 := rew2_spec cap E (R 14) (J1 + (ys.flatMap intWord).length)
    (bSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E p (J1 + (ys.flatMap intWord).length) 0 (bfold p x ys))
    (by simp [bSt, at2]) (by omega) (by simp [bSt, at2])
  have e5 : ((bSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E p (J1 + (ys.flatMap intWord).length) 0
      (bfold p x ys)).setv (R 14) 0).seth E 0 =
      ((((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 23) (bfold p x ys)).setv (R 24) (p - bfold p x ys)) := by
    have h14 := hz 14 (by decide)
    unfold bSt; clear d1 d2 d3 d4 d5 e3 hz
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y1 : y = R 14
      · rw [y1]; simp_all [at2, Function.update_apply]
      by_cases y2 : y = R 20
      · rw [y2]; simp_all [at2, Function.update_apply]
      by_cases y3 : y = R 23
      · rw [y3]; simp_all [at2, Function.update_apply]
      by_cases y4 : y = R 24
      · rw [y4]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e5] at d5
  have d6 := wclear_spec cap (R 15) S ((((σ.setv (R 15) S).setv (R 17) (g / m)).setv (R 23) (bfold p x ys)).setv (R 24)
    (p - bfold p x ys)) (by simp) (by simp; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_ (by
    unfold cBCost; rw [hys] at d4 ⊢; omega)
  clear d1 d2 d3 d4 d5 d6 e3 e5
  have h15 := hz 15 (by decide)
  clear hz
  refine WState.eq ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · funext y
    by_cases y1 : y = R 15
    · rw [y1]; simp_all [Function.update_apply]
    by_cases y2 : y = R 17
    · rw [y2]; simp_all [Function.update_apply]
    by_cases y3 : y = R 23
    · rw [y3]; simp_all [Function.update_apply]
    by_cases y4 : y = R 24
    · rw [y4]; simp_all [Function.update_apply]
    simp_all [Function.update_apply]
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
