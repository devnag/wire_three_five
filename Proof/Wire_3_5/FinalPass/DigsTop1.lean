import Proof.Wire_3_5.FinalPass.DigsPass4

/-! # `DigsW`'s body, part 14: the whole program (P3:2585-2599, W17)

`topW` = the base pass (`R 23 = base mod p`, `R 24 = p − R 23`), `R 35 := τ₀`, the `τ₀` digits, the output rewound
(`WM.rewind` by the written length `R 34`), and `R 23`, `R 24`, `R 36` cleared. From an entry with the inputs in
`R 0 … R 4`, every other register zero and the output stream blank, it leaves exactly `σ.sets Dg (Wd … [] τ₀)`.
Main declarations: `allL`, `topB`, **`top_spec`**. Paper quantity: the digit populations of row `(g, p)` as one
word on `Dg`. -/

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

/-- Every register but the five inputs. -/
def allL : List (Fin digsK) :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34,
    35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The whole program. -/
def topW (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (baseW R Pay) (.seq (Hash4.wcopyR (R 3) (R 35) (R 39)) (.seq (digitsW R Pay Dg) (.seq (WM.rewind Dg (R 34))
    (.seq (WM.clear (R 23)) (.seq (WM.clear (R 24)) (WM.clear (R 36)))))))

/-- The whole program's bound. -/
def topB (U : ℕ) : ℕ :=
  bB U + 1 + (18 * U + 4 + ((U * (dB U + 4) + 1) + 1 + ((5 * U + 1) + 1 + (3 * U + 2 + (3 * U + 2 + (3 * U + 1))))))

theorem top_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ) (ha : a' ≤ 4)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (t : ℕ → ℤ) (rest : ℕ → List Bool)
    (G p τ off U : ℕ) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i ++ [t i]).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p)
    (hDs : σ.st Dg = []) (hDh : σ.sh Dg = 0)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (hT : σ.val (R 3) = τ)
    (hov : σ.val (R 4) = off) (hz : Zs R σ allL)
    (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U) (hpU : p ≤ U) (hτU : τ ≤ U)
    (hlU : (Wd a' off (Bf p (fun i => ws i ++ [t i]) a') p S ws [] τ).length + off + Os S a' + 2 ≤ U) (haU : a' ≤ U)
    (hU : 2 * U + 2 ≤ cap) :
    WExec cap (topW R Pay Dg) σ (σ.sets Dg (Wd a' off (Bf p (fun i => ws i ++ [t i]) a') p S ws [] τ)) (topB U) := by
  obtain ⟨bm, hbm⟩ : ∃ b, b = Bf p (fun i => ws i ++ [t i]) a' := ⟨_, rfl⟩
  rw [← hbm] at hlU ⊢
  have hbmp : bm < p := by rw [hbm]; exact Bf_lt p hp _ a'
  obtain ⟨W, hW⟩ : ∃ W, W = Wd a' off bm p S ws [] τ := ⟨_, rfl⟩
  rw [← hW] at hlU ⊢
  have h35 := hz 35 (by decide)
  have h36 := hz 36 (by decide)
  have h34 := hz 34 (by decide)
  have h39 := hz 39 (by decide)
  have h23z := hz 23 (by decide)
  have h24z := hz 24 (by decide)
  -- the base
  have d1 := base_spec cap R Pay a' ha cD S m zs (fun i => ws i ++ [t i]) rest G p U σ hst hs hc hzs
    (fun i hi => by simp [hws i hi]) hm hGa hp hA hG hP (Zs_sub R _ _ _ (by decide) hz) hcU hmU hGU hpU haU hU
  rw [← hbm] at d1
  -- τ₀
  have d2 := Hash4.wcopyR_spec cap (R 3) (R 35) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((σ.setv (R 23) bm).setv (R 24) (p - bm)) (by simp [h35]) (by simp [h39])
    (by simp [hT]; omega)
  rw [show ((σ.setv (R 23) bm).setv (R 24) (p - bm)).val (R 3) = τ by simp [hT]] at d2
  have e2 : (((σ.setv (R 23) bm).setv (R 24) (p - bm)).setv (R 35) τ) =
      digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ (Wd a' off bm p S ws [] 0) 0 := by
    unfold digSt; simp only [Wd, List.range_zero, List.flatMap_nil, List.append_nil, Nat.sub_zero]
    clear d1 d2 hz
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y1 : y = R 35
      · rw [y1]; simp_all [outAt, Function.update_apply]
      by_cases y2 : y = R 36
      · rw [y2]; simp_all [outAt, Function.update_apply]
      by_cases y3 : y = R 34
      · rw [y3]; simp_all [outAt, Function.update_apply]
      simp_all [outAt, Function.update_apply]
    · rfl
  rw [e2] at d2
  -- the digits
  have d3 := digits_spec cap R Pay Dg hPD a' ha cD S m zs ws (fun i => [intWord (t i)].flatten ++ rest i) G p bm off τ
    U [] ((σ.setv (R 23) bm).setv (R 24) (p - bm)) (fun i hi => by simp [hst i hi]) (fun i hi => by simp [hs i hi])
    (fun i hi => by rw [hc i hi]; simp [List.flatMap_append]) hzs hws hm hGa hp hbmp (by simp [hA]) (by simp [hG])
    (by simp [hP]) (by simp) (by simp [hov])
    (Zs_setv R _ _ _ _ (by decide) (Zs_setv R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz)))
    hcU hmU hGU hpU hτU (by rw [← hW]; exact hlU) haU hU
  rw [← hW] at d3
  -- rewind, clear
  have d4 := wrewind_spec cap Dg (R 34) W.length (digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ W τ)
    (by simp [digSt]) (by simp [digSt]; omega)
  have d5 := wclear_spec cap (R 23) bm (((digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ W τ).setv (R 34)
    0).seth Dg ((digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ W τ).sh Dg - W.length))
    (by simp [digSt, outAt]) (by simp [digSt, outAt]; omega)
  have d6 := wclear_spec cap (R 24) (p - bm) (((((digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ W τ).setv
    (R 34) 0).seth Dg ((digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ W τ).sh Dg - W.length)).setv (R 23) 0))
    (by simp [digSt, outAt]) (by simp [digSt, outAt]; omega)
  have d7 := wclear_spec cap (R 36) τ ((((((digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ W τ).setv
    (R 34) 0).seth Dg ((digSt R ((σ.setv (R 23) bm).setv (R 24) (p - bm)) Dg τ W τ).sh Dg - W.length)).setv (R 23)
    0)).setv (R 24) 0) (by simp [digSt, outAt]) (by simp [digSt, outAt]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6 d7))))))
    ?_ (by unfold topB; have := Nat.mul_le_mul_right (dB U + 4) hτU; omega)
  unfold digSt
  clear d1 d2 d3 d4 d5 d6 d7 e2 hz
  refine WState.eq ?_ ?_ ?_ ?_
  · funext i
    simp only [outAt, WState.setv_sh, WState.seth_sh, WState.sets_sh, Function.update_apply]
    split_ifs <;> simp_all
  · wst_st
  · funext y
    by_cases y1 : y = R 23
    · rw [y1]; simp_all [outAt, Function.update_apply]
    by_cases y2 : y = R 24
    · rw [y2]; simp_all [outAt, Function.update_apply]
    by_cases y3 : y = R 34
    · rw [y3]; simp_all [outAt, Function.update_apply]
    by_cases y4 : y = R 35
    · rw [y4]; simp_all [outAt, Function.update_apply]
    by_cases y5 : y = R 36
    · rw [y5]; simp_all [outAt, Function.update_apply]
    simp_all [outAt, Function.update_apply]
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
