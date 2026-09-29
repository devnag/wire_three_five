import Proof.Wire_3_5.FinalPass.DigsPass3

/-! # `DigsW`'s body, part 13: the stack base modulo `p` (P3:2543-2551)

`baseW`: `R 17 := g`, `R 23 := 1`, `R 24 := p − 1`, `R 38 := a'`, then `cBodyBW` on payload `i` for `i < a'`. The
running residue before circuit `i` is `Bf i` (`Bf 0 = 1`, `Bf (i + 1) = bfold p (Bf i) ys_i`). Main declarations:
`Bf`, `bcSt`, **`base_spec`**. Paper quantity: `base mod p`, `base = 1 + Σ_i ‖child_i‖` (`EqRef.baseOf`). -/

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

/-- The running residue of the stack base before circuit `i`. -/
def Bf (p : ℕ) (ys : ℕ → List ℤ) : ℕ → ℕ
  | 0 => 1
  | i + 1 => bfold p (Bf p ys i) (ys i)

theorem Bf_lt (p : ℕ) (hp : 2 ≤ p) (ys : ℕ → List ℤ) : ∀ i, Bf p ys i < p
  | 0 => by simp [Bf]; omega
  | i + 1 => bfold_lt p _ (by omega) (Bf_lt p hp ys i) (ys i)

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The base pass. -/
def baseW (Pay : Fin 4 → Fin (ns + 1)) : WM ns nr :=
  .seq (Hash4.wcopyR (R 1) (R 17) (R 39)) (.seq (.inc (R 23)) (.seq (Hash4.wcopyR (R 2) (R 24) (R 39))
    (.seq (.dec (R 24)) (.seq (Hash4.wcopyR (R 0) (R 38) (R 39)) (circW (R 38) (fun i => cBodyBW R (Pay i)))))))

/-- The base pass's circuit-loop state. -/
def bcSt (σ : WState ns nr) (a' G p : ℕ) (m : ℕ → ℕ) (ys : ℕ → List ℤ) (i : ℕ) : WState ns nr :=
  (((σ.setv (R 17) (Gs G m i)).setv (R 23) (Bf p ys i)).setv (R 24) (p - Bf p ys i)).setv (R 38) (a' - i)

/-- The base pass's uniform bound. -/
def bB (U : ℕ) : ℕ :=
  18 * U + 3 + 1 + (3 + 1 + (18 * U + 3 + 1 + (1 + 1 + (18 * U + 3 + 1 + (4 * (cBB U + 3) + 3)))))

/-- The base pass's zero registers. -/
def bL : List (Fin digsK) :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 38, 39, 40]

theorem base_spec (Pay : Fin 4 → Fin (ns + 1)) (a' : ℕ) (ha : a' ≤ 4) (cD : ℕ → List Bool) (S m : ℕ → ℕ)
    (zs ys : ℕ → List ℤ) (rest : ℕ → List Bool) (G p U : ℕ) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ys i).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hys : ∀ i, i < a' → (ys i).length = S i + 1)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (hz : Zs R σ bL)
    (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U) (hpU : p ≤ U)
    (haU : a' ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (baseW R Pay) σ ((σ.setv (R 23) (Bf p ys a')).setv (R 24) (p - Bf p ys a')) (bB U) := by
  have h17 := hz 17 (by decide)
  have h23 := hz 23 (by decide)
  have h24 := hz 24 (by decide)
  have h38 := hz 38 (by decide)
  have h39 := hz 39 (by decide)
  have d1 := Hash4.wcopyR_spec cap (R 1) (R 17) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) σ h17 h39 (by omega)
  rw [hG] at d1
  have d2 := WExec.inc (cap := cap) (R 23) (σ.setv (R 17) G) (by simp [h23]; omega)
  rw [show (σ.setv (R 17) G).val (R 23) + 1 = 1 by simp [h23]] at d2
  have d3 := Hash4.wcopyR_spec cap (R 2) (R 24) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((σ.setv (R 17) G).setv (R 23) 1) (by simp [h24]) (by simp [h39])
    (by simp [hP]; omega)
  rw [show ((σ.setv (R 17) G).setv (R 23) 1).val (R 2) = p by simp [hP]] at d3
  have d4 := WExec.dec (cap := cap) (R 24) (((σ.setv (R 17) G).setv (R 23) 1).setv (R 24) p) (by simp; omega)
  rw [show (((σ.setv (R 17) G).setv (R 23) 1).setv (R 24) p).val (R 24) - 1 = p - 1 by simp] at d4
  have d5 := Hash4.wcopyR_spec cap (R 0) (R 38) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((((σ.setv (R 17) G).setv (R 23) 1).setv (R 24) p).setv (R 24) (p - 1))
    (by simp [h38]) (by simp [h39]) (by simp [hA]; omega)
  rw [show ((((σ.setv (R 17) G).setv (R 23) 1).setv (R 24) p).setv (R 24) (p - 1)).val (R 0) = a' by simp [hA]] at d5
  have e5 : (((((σ.setv (R 17) G).setv (R 23) 1).setv (R 24) p).setv (R 24) (p - 1)).setv (R 38) a') =
      bcSt R σ a' G p m ys 0 := by
    unfold bcSt; simp only [Gs, Bf, Nat.sub_zero]
    clear d1 d2 d3 d4 d5 hz
    refine WState.eq rfl rfl ?_ rfl
    funext y
    by_cases y1 : y = R 17
    · rw [y1]; simp_all [Function.update_apply]
    by_cases y2 : y = R 23
    · rw [y2]; simp_all [Function.update_apply]
    by_cases y3 : y = R 24
    · rw [y3]; simp_all [Function.update_apply]
    by_cases y4 : y = R 38
    · rw [y4]; simp_all [Function.update_apply]
    simp_all [Function.update_apply]
  rw [e5] at d5
  have d6 := circ_spec cap (R 38) (fun i => cBodyBW R (Pay i)) a' (cBB U) ha (by omega) (bcSt R σ a' G p m ys)
    (fun k _ => by simp [bcSt]) (fun i hi => by
      have hci := hc i.val hi
      have hlen : (cD i.val).length = (natWord (S i.val)).length + (natWord (m i.val)).length +
          ((zs i.val).flatMap intWord).length + ((ys i.val).flatMap intWord).length + (rest i.val).length := by
        rw [hci]; simp only [List.length_append]; ring
      have hyl := fm_len_ge (ys i.val)
      have hzl := fm_len_ge (zs i.val)
      have hysi := hys i.val hi
      have hGi := Gs_le G m i.val
      have hBi := Bf_lt p hp ys i.val
      have dx := cBodyB_spec cap R (Pay i) (S i.val) (m i.val) (Gs G m i.val) (zs i.val) (ys i.val) (cD i.val)
        (rest i.val) p (Bf p ys i.val) U ((bcSt R σ a' G p m ys i.val).setv (R 38) (a' - i.val - 1))
        (by simp [bcSt, hst i hi]) (by simp [bcSt, hs i hi]) hci (hzs i.val hi) hysi (hm i.val hi) (by omega) hBi
        (by simp [bcSt]) (by simp [bcSt]) (by simp [bcSt]) (by simp [bcSt, hP])
        (fun r hr => by
          have r17 : r ≠ 17 := by rintro rfl; revert hr; decide
          have r23 : r ≠ 23 := by rintro rfl; revert hr; decide
          have r24 : r ≠ 24 := by rintro rfl; revert hr; decide
          have r38 : r ≠ 38 := by rintro rfl; revert hr; decide
          have := hz r (by revert hr; revert r; decide)
          simp [bcSt, Function.update_apply, R.injective.ne r17, R.injective.ne r23, R.injective.ne r24,
            R.injective.ne r38, this])
        (hcU i.val hi) (hmU i.val hi) (le_trans hGi hGU) hpU hU
      refine WExec.cast cap dx ?_ (cBCost_le _ _ _ _ _ _ _ U (by have := hcU i.val hi; omega) (hmU i.val hi)
        (le_trans hGi hGU) (by have := hcU i.val hi; omega) (hcU i.val hi) hpU (by have := hcU i.val hi; omega))
      show _ = (((σ.setv (R 17) (Gs G m i.val / m i.val)).setv (R 23) (bfold p (Bf p ys i.val) (ys i.val))).setv
        (R 24) (p - bfold p (Bf p ys i.val) (ys i.val))).setv (R 38) (a' - (i.val + 1))
      rw [show a' - (i.val + 1) = a' - i.val - 1 by omega]
      unfold bcSt
      clear dx hz
      refine WState.eq rfl rfl ?_ rfl
      funext y
      by_cases y1 : y = R 17
      · rw [y1]; simp_all [Function.update_apply]
      by_cases y2 : y = R 23
      · rw [y2]; simp_all [Function.update_apply]
      by_cases y3 : y = R 24
      · rw [y3]; simp_all [Function.update_apply]
      by_cases y4 : y = R 38
      · rw [y4]; simp_all [Function.update_apply]
      simp_all [Function.update_apply])
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_
    (by unfold bB; omega)
  unfold bcSt
  clear d1 d2 d3 d4 d5 d6 e5 hz
  refine WState.eq rfl rfl ?_ rfl
  funext y
  by_cases y1 : y = R 17
  · rw [y1]; simp_all [Function.update_apply]
  by_cases y2 : y = R 23
  · rw [y2]; simp_all [Function.update_apply]
  by_cases y3 : y = R 24
  · rw [y3]; simp_all [Function.update_apply]
  by_cases y4 : y = R 38
  · rw [y4]; simp_all [Function.update_apply]
  simp_all [Function.update_apply]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
