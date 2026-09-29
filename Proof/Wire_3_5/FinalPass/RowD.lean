import Proof.Wire_3_5.FinalPass.RowChain

/-! # `RowW`, part 4: the target pass and the coefficient pass (P3:2585-2592)

`tPassW`: `R 17 := g`, `R 25 := 1`, `R 42 := p`, `R 38 := a'`, then `tBodyW` on payload `i < a'`: `R 41` ends at
`Tf a' = Σ_i base^i t_i mod p` (as a running residue). `aPassW`: `R 17 := g`, `R 25 := 1`, `R 38 := a'`, then
`cBodyAW` on each payload: the output grows by `La`, circuit `i`'s coefficients in unary. Main declarations: `Tf`,
`tPass_spec`, `La`, **`aPass_spec`**. Paper quantities: the target of `L_g` modulo `p` and the reduced
coefficients `a_i` of row `(g, p)`. -/

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

/-- The target's running residue before circuit `i`. -/
def Tf (bm p : ℕ) (t : ℕ → ℤ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => (Tf bm p t i + Bs bm p i * (t i % (p : ℤ)).toNat % p) % p

theorem Tf_lt (bm p : ℕ) (hp : 1 ≤ p) (t : ℕ → ℤ) : ∀ i, Tf bm p t i < p
  | 0 => by simp [Tf]; omega
  | i + 1 => Nat.mod_lt _ (by omega)

/-- The coefficient pass's output before circuit `i`. -/
def La (bm p : ℕ) (ws : ℕ → List ℤ) (l : List Bool) : ℕ → List Bool
  | 0 => l
  | i + 1 => La bm p ws l i ++ aWord (Bs bm p i) p (ws i)

theorem La_mono (bm p : ℕ) (ws : ℕ → List ℤ) (l : List Bool) (i : ℕ) :
    ∀ j, i ≤ j → (La bm p ws l i).length ≤ (La bm p ws l j).length
  | 0, h => by rw [Nat.le_zero.mp h]
  | j + 1, h => by
    rcases Nat.lt_or_ge i (j + 1) with h' | h'
    · have := La_mono bm p ws l i j (by omega); simp [La]; omega
    · rw [show i = j + 1 by omega]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The target pass. -/
def tPassW (Pay : Fin 4 → Fin (ns + 1)) : WM ns nr :=
  .seq (Hash4.wcopyR (R 1) (R 17) (R 39)) (.seq (.inc (R 25)) (.seq (Hash4.wcopyR (R 2) (R 42) (R 39))
    (.seq (Hash4.wcopyR (R 0) (R 38) (R 39)) (.seq (circW (R 38) (fun i => tBodyW R (Pay i))) (WM.clear (R 25))))))

/-- The target pass's circuit-loop state. -/
def tcSt (σ : WState ns nr) (a' G bm p : ℕ) (m : ℕ → ℕ) (t : ℕ → ℤ) (i : ℕ) : WState ns nr :=
  ((((σ.setv (R 17) (Gs G m i)).setv (R 25) (Bs bm p i)).setv (R 41) (Tf bm p t i)).setv (R 42)
    (p - Tf bm p t i)).setv (R 38) (a' - i)

/-- One target circuit's uniform bound. -/
def tB (U : ℕ) : ℕ :=
  navB U + 1 + (18 * U + 3 + 1 + ((U * (24 * U + 23) + 1) + 1 + (modCost2 U U + 1 + (18 * U + 3 + 1 +
    (U * ThrArith.mulStep U + 1 + 1 + (3 * U + 1 + 1 + (U * (7 * U + 12) + 1 + 1 + ((7 * U + 3) + 1 +
    (bUpdCost U + 1 + (3 * U + 1))))))))))

theorem tCost_le (S m g nz Lm p J U : ℕ) (hS : S ≤ U) (hm : m ≤ U) (hg : g ≤ U) (hn : nz ≤ U) (hL : Lm ≤ U)
    (hp : p ≤ U) (hJ : J ≤ U) : tCost S m g nz Lm p J ≤ tB U := by
  unfold tCost tB
  have h1 := navCost_le S m g nz Lm U hS hm hg hn hL
  have h2 := modCost2_le Lm p U U hL hp
  have h3 := mulStep_le p U hp
  have h4 := bUpdCost_le p U hp
  gcongr

/-- The target pass's bound. -/
def tPB (U : ℕ) : ℕ := 18 * U + 4 + (4 + (18 * U + 4 + (18 * U + 4 + ((4 * (tB U + 3) + 3) + 1 + (3 * U + 1)))))

/-- The target pass's zero registers. -/
def tpL : List (Fin digsK) :=
  [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 25, 26, 27, 28, 29, 30, 31, 32, 33, 38, 39,
    40, 41, 42]

theorem tcSt_succ (σ : WState ns nr) (a' G bm p : ℕ) (m : ℕ → ℕ) (t : ℕ → ℤ) (i : ℕ) :
    tcSt R σ a' G bm p m t (i + 1) = ((((σ.setv (R 17) (Gs G m i / m i)).setv (R 25) (Bs bm p i * bm % p)).setv (R 41)
      ((Tf bm p t i + Bs bm p i * (t i % (p : ℤ)).toNat % p) % p)).setv (R 42)
      (p - (Tf bm p t i + Bs bm p i * (t i % (p : ℤ)).toNat % p) % p)).setv (R 38) (a' - (i + 1)) := rfl

/-- One target circuit's state step. -/
theorem tc_step_eq (σ : WState ns nr) (a' G bm p : ℕ) (m : ℕ → ℕ) (t : ℕ → ℤ) (i : ℕ) :
    (((((tcSt R σ a' G bm p m t i).setv (R 38) (a' - i - 1)).setv (R 17) (Gs G m i / m i)).setv (R 25)
      (Bs bm p i * bm % p)).setv (R 41) ((Tf bm p t i + Bs bm p i * (t i % (p : ℤ)).toNat % p) % p)).setv (R 42)
      (p - (Tf bm p t i + Bs bm p i * (t i % (p : ℤ)).toNat % p) % p) = tcSt R σ a' G bm p m t (i + 1) := by
  rw [tcSt_succ, show a' - (i + 1) = a' - i - 1 by omega]
  unfold tcSt
  exact chain5 σ (R 17) (R 25) (R 41) (R 42) (R 38) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (R.injective.ne (by decide)) _ _ _ _ _ _ _ _ _ _

theorem tStep_spec (Pay : Fin 4 → Fin (ns + 1)) (a' : ℕ) (cD : ℕ → List Bool) (S m : ℕ → ℕ)
    (zs ws : ℕ → List ℤ) (t : ℕ → ℤ) (rest : ℕ → List Bool) (G p bm U : ℕ) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i).flatMap intWord ++ (intWord (t i) ++ rest i)))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hp : 2 ≤ p) (hbm : bm < p) (hP : σ.val (R 2) = p) (h23 : σ.val (R 23) = bm)
    (hz : Zs R σ tpL) (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U)
    (hpU : p ≤ U) (hU : 2 * U + 2 ≤ cap) (i : Fin 4) (hi : i.val < a') :
    WExec cap (tBodyW R (Pay i)) ((tcSt R σ a' G bm p m t i.val).setv (R 38) (a' - i.val - 1))
      (tcSt R σ a' G bm p m t (i.val + 1)) (tB U) := by
  have hci := hc i.val hi
  have hlen : (cD i.val).length = (natWord (S i.val)).length + (natWord (m i.val)).length +
      ((zs i.val).flatMap intWord).length + ((ws i.val).flatMap intWord).length + (intWord (t i.val)).length +
      (rest i.val).length := by
    rw [hci]; simp only [List.length_append]; ring
  have hwl := fm_len_ge (ws i.val)
  have hzl := fm_len_ge (zs i.val)
  have hwsi := hws i.val hi
  have hGi := Gs_le G m i.val
  have hBi := Bs_lt bm p hp i.val
  have hTi := Tf_lt bm p (by omega) t i.val
  have hcUi := hcU i.val hi
  have dx := tBody_spec cap R (Pay i) (S i.val) (m i.val) (Gs G m i.val) (zs i.val) (ws i.val) (t i.val)
    (cD i.val) (rest i.val) p (Bs bm p i.val) bm (Tf bm p t i.val) U
    ((tcSt R σ a' G bm p m t i.val).setv (R 38) (a' - i.val - 1))
    (by simp [tcSt, hst i hi]) (by simp [tcSt, hs i hi]) hci (hzs i.val hi) hwsi (hm i.val hi)
    (by omega) hBi hbm hTi (by simp [tcSt]) (by simp [tcSt]) (by simp [tcSt, h23]) (by simp [tcSt, hP])
    (by simp [tcSt]) (by simp [tcSt])
    (fun r hr => by
      have r17 : r ≠ 17 := by rintro rfl; revert hr; decide
      have r25 : r ≠ 25 := by rintro rfl; revert hr; decide
      have r38 : r ≠ 38 := by rintro rfl; revert hr; decide
      have r41 : r ≠ 41 := by rintro rfl; revert hr; decide
      have r42 : r ≠ 42 := by rintro rfl; revert hr; decide
      have := hz r (by revert hr; revert r; decide)
      simp [tcSt, Function.update_apply, R.injective.ne r17, R.injective.ne r25, R.injective.ne r38,
        R.injective.ne r41, R.injective.ne r42, this])
    hcUi (hmU i.val hi) (le_trans hGi hGU) hpU hU
  rw [tc_step_eq R σ a' G bm p m t i.val] at dx
  exact WExec.mono dx (tCost_le _ _ _ _ _ _ _ U (by omega) (hmU i.val hi) (le_trans hGi hGU) (by omega) hcUi hpU
    (by omega))

theorem tPass_spec (Pay : Fin 4 → Fin (ns + 1)) (a' : ℕ) (ha : a' ≤ 4) (cD : ℕ → List Bool) (S m : ℕ → ℕ)
    (zs ws : ℕ → List ℤ) (t : ℕ → ℤ) (rest : ℕ → List Bool) (G p bm U : ℕ) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i).flatMap intWord ++ (intWord (t i) ++ rest i)))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p) (hbm : bm < p)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (h23 : σ.val (R 23) = bm)
    (hz : Zs R σ tpL) (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U)
    (hpU : p ≤ U) (haU : a' ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (tPassW R Pay) σ ((σ.setv (R 41) (Tf bm p t a')).setv (R 42) (p - Tf bm p t a')) (tPB U) := by
  have h17 := hz 17 (by decide)
  have h25 := hz 25 (by decide)
  have h38 := hz 38 (by decide)
  have h39 := hz 39 (by decide)
  have h41 := hz 41 (by decide)
  have h42 := hz 42 (by decide)
  have d1 := Hash4.wcopyR_spec cap (R 1) (R 17) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) σ h17 h39 (by omega)
  rw [hG] at d1
  have d2 := WExec.inc (cap := cap) (R 25) (σ.setv (R 17) G) (by simp [h25]; omega)
  rw [show (σ.setv (R 17) G).val (R 25) + 1 = 1 by simp [h25]] at d2
  have d3 := Hash4.wcopyR_spec cap (R 2) (R 42) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((σ.setv (R 17) G).setv (R 25) 1) (by simp [h42]) (by simp [h39])
    (by simp [hP]; omega)
  rw [show ((σ.setv (R 17) G).setv (R 25) 1).val (R 2) = p by simp [hP]] at d3
  have d4 := Hash4.wcopyR_spec cap (R 0) (R 38) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (((σ.setv (R 17) G).setv (R 25) 1).setv (R 42) p) (by simp [h38]) (by simp [h39])
    (by simp [hA]; omega)
  rw [show (((σ.setv (R 17) G).setv (R 25) 1).setv (R 42) p).val (R 0) = a' by simp [hA]] at d4
  have e4 : ((((σ.setv (R 17) G).setv (R 25) 1).setv (R 42) p).setv (R 38) a') = tcSt R σ a' G bm p m t 0 := by
    unfold tcSt; simp only [Gs, Bs, Tf, Nat.sub_zero]
    clear d1 d2 d3 d4 hz
    refine WState.eq rfl rfl ?_ rfl
    funext y
    by_cases y1 : y = R 17
    · rw [y1]; simp_all [Function.update_apply]
    by_cases y2 : y = R 25
    · rw [y2]; simp_all [Function.update_apply]
    by_cases y3 : y = R 41
    · rw [y3]; simp_all [Function.update_apply]
    by_cases y4 : y = R 42
    · rw [y4]; simp_all [Function.update_apply]
    by_cases y5 : y = R 38
    · rw [y5]; simp_all [Function.update_apply]
    simp_all [Function.update_apply]
  rw [e4] at d4
  have d5 := circ_spec cap (R 38) (fun i => tBodyW R (Pay i)) a' (tB U) ha (by omega) (tcSt R σ a' G bm p m t)
    (fun k _ => by simp [tcSt]) (tStep_spec cap R Pay a' cD S m zs ws t rest G p bm U σ hst hs hc hzs hws hm hp hbm hP
      h23 hz hcU hmU hGU hpU hU)
  have hBa := Bs_lt bm p hp a'
  have d6 := wclear_spec cap (R 25) (Bs bm p a') (tcSt R σ a' G bm p m t a') (by simp [tcSt]) (by simp [tcSt]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_
    (by unfold tPB; omega)
  unfold tcSt
  clear d1 d2 d3 d4 d5 d6 e4 hz
  refine WState.eq rfl rfl ?_ rfl
  funext y
  by_cases y1 : y = R 17
  · rw [y1]; simp_all [Function.update_apply]
  by_cases y2 : y = R 25
  · rw [y2]; simp_all [Function.update_apply]
  by_cases y3 : y = R 41
  · rw [y3]; simp_all [Function.update_apply]
  by_cases y4 : y = R 42
  · rw [y4]; simp_all [Function.update_apply]
  by_cases y5 : y = R 38
  · rw [y5]; simp_all [Function.update_apply]
  simp_all [Function.update_apply]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
