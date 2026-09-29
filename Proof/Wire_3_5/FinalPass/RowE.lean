import Proof.Wire_3_5.FinalPass.RowChain2

/-! # `RowW`, part 5: the coefficient pass (P3:2585-2592)

`aPassW`: `R 17 := g`, `R 25 := 1`, `R 38 := a'`, then `cBodyAW` on payload `i < a'`, then `R 25` cleared; the output
grows by `La a'`, every circuit's coefficients in unary. Main declarations: `acSt`, `ac_step_eq`, `aStep_spec`,
**`aPass_spec`**. Paper quantity: the reduced coefficients `a_i` of row `(g, p)` in occurrence order. -/

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

/-- The coefficient pass. -/
def aPassW (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (Hash4.wcopyR (R 1) (R 17) (R 39)) (.seq (.inc (R 25)) (.seq (Hash4.wcopyR (R 0) (R 38) (R 39))
    (.seq (circW (R 38) (fun i => cBodyAW R (Pay i) Dg)) (WM.clear (R 25)))))

/-- The coefficient pass's circuit-loop state. -/
def acSt (σ : WState ns nr) (Dg : Fin (ns + 1)) (a' G bm p : ℕ) (m : ℕ → ℕ) (ws : ℕ → List ℤ) (l : List Bool)
    (i : ℕ) : WState ns nr :=
  outAt (((σ.setv (R 17) (Gs G m i)).setv (R 25) (Bs bm p i)).setv (R 38) (a' - i)) Dg (R 34) (La bm p ws l i)

theorem ac_step_eq (σ : WState ns nr) (Dg : Fin (ns + 1)) (a' G bm p : ℕ) (m : ℕ → ℕ) (ws : ℕ → List ℤ)
    (l : List Bool) (i : ℕ) :
    outAt ((((acSt R σ Dg a' G bm p m ws l i).setv (R 38) (a' - i - 1)).setv (R 17) (Gs G m i / m i)).setv (R 25)
      (Bs bm p i * bm % p)) Dg (R 34) (La bm p ws l i ++ aWord (Bs bm p i) p (ws i)) =
      acSt R σ Dg a' G bm p m ws l (i + 1) := by
  unfold acSt
  rw [← outAt_setv _ _ _ _ (R 38) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 17) (R.injective.ne (by decide)),
    ← outAt_setv _ _ _ _ (R 25) (R.injective.ne (by decide)), outAt_outAt,
    chain3 σ (R 17) (R 25) (R 38) (R.injective.ne (by decide)) (R.injective.ne (by decide))
      (R.injective.ne (by decide)), show a' - (i + 1) = a' - i - 1 by omega]
  rfl

/-- One coefficient circuit's uniform bound. -/
def cAB (U : ℕ) : ℕ :=
  navB U + 1 + (18 * U + 3 + 1 + ((U * (aCost U U + 4) + 1) + 1 + ((7 * U + 3) + 1 + (bUpdCost U + 1 + (3 * U + 1)))))

theorem aCost_le (L p U : ℕ) (hL : L ≤ U) (hp : p ≤ U) : aCost L p ≤ aCost U U := by
  unfold aCost
  have h1 := modCost2_le L p U U hL hp
  have h2 := mulStep_le p U hp
  gcongr

theorem cACost_le (S m g nz Lm p J U : ℕ) (hS : S ≤ U) (hm : m ≤ U) (hg : g ≤ U) (hn : nz ≤ U) (hL : Lm ≤ U)
    (hp : p ≤ U) (hJ : J ≤ U) : cACost S m g nz Lm p J ≤ cAB U := by
  unfold cACost cAB
  have h1 := navCost_le S m g nz Lm U hS hm hg hn hL
  have h2 := aCost_le Lm p U hL hp
  have h3 := bUpdCost_le p U hp
  gcongr

theorem aStep_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (rest : ℕ → List Bool) (G p bm U : ℕ) (l : List Bool)
    (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hp : 2 ≤ p) (hbm : bm < p) (hP : σ.val (R 2) = p) (h23 : σ.val (R 23) = bm)
    (hz : Zs R σ cL) (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U)
    (hlU : (La bm p ws l a').length + p + 1 ≤ U) (hU : 2 * U + 2 ≤ cap) (i : Fin 4) (hi : i.val < a') :
    WExec cap (cBodyAW R (Pay i) Dg) ((acSt R σ Dg a' G bm p m ws l i.val).setv (R 38) (a' - i.val - 1))
      (acSt R σ Dg a' G bm p m ws l (i.val + 1)) (cAB U) := by
  have hci := hc i.val hi
  have hlen : (cD i.val).length = (natWord (S i.val)).length + (natWord (m i.val)).length +
      ((zs i.val).flatMap intWord).length + ((ws i.val).flatMap intWord).length + (rest i.val).length := by
    rw [hci]; simp only [List.length_append]; ring
  have hwl := fm_len_ge (ws i.val)
  have hzl := fm_len_ge (zs i.val)
  have hwsi := hws i.val hi
  have hGi := Gs_le G m i.val
  have hBi := Bs_lt bm p hp i.val
  have hcUi := hcU i.val hi
  have hLm := La_mono bm p ws l (i.val + 1) a' hi
  have dx := cBodyA_spec cap R (Pay i) Dg (hPD i) (S i.val) (m i.val) (Gs G m i.val) (zs i.val) (ws i.val) (cD i.val)
    (rest i.val) p (Bs bm p i.val) bm U (La bm p ws l i.val)
    ((acSt R σ Dg a' G bm p m ws l i.val).setv (R 38) (a' - i.val - 1))
    (by simp [acSt, outAt, Function.update_apply, hPD i, hst i hi])
    (by simp [acSt, outAt, Function.update_apply, hPD i, hs i hi]) hci (hzs i.val hi) hwsi (hm i.val hi) (by omega) hBi
    hbm (by simp [acSt]) (by simp [acSt]) (by simp [acSt]) (by simp [acSt, outAt]) (by simp [acSt, outAt])
    (by simp [acSt, outAt, h23]) (by simp [acSt, outAt, hP])
    (fun r hr => by
      have r17 : r ≠ 17 := by rintro rfl; revert hr; decide
      have r25 : r ≠ 25 := by rintro rfl; revert hr; decide
      have r38 : r ≠ 38 := by rintro rfl; revert hr; decide
      have r34 : r ≠ 34 := by rintro rfl; revert hr; decide
      have := hz r hr
      simp [acSt, outAt, Function.update_apply, R.injective.ne r17, R.injective.ne r25, R.injective.ne r38,
        R.injective.ne r34, this])
    hcUi (hmU i.val hi) (le_trans hGi hGU) (by simp [La] at hLm; simp only [List.length_append]; omega) hU
  rw [ac_step_eq R σ Dg a' G bm p m ws l i.val] at dx
  exact WExec.mono dx (cACost_le _ _ _ _ _ _ _ U (by omega) (hmU i.val hi) (le_trans hGi hGU) (by omega) hcUi
    (by omega) (by omega))

/-- The coefficient pass's bound. -/
def aPB (U : ℕ) : ℕ := 18 * U + 4 + (4 + (18 * U + 4 + ((4 * (cAB U + 3) + 3) + 1 + (3 * U + 1))))

theorem aPass_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ) (ha : a' ≤ 4)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (rest : ℕ → List Bool) (G p bm U : ℕ) (l : List Bool)
    (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p) (hbm : bm < p)
    (hlst : σ.st Dg = l) (hlsh : σ.sh Dg = l.length) (hlw : σ.val (R 34) = l.length)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (h23 : σ.val (R 23) = bm)
    (hz : Zs R σ dL) (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U)
    (hpU : p ≤ U) (haU : a' ≤ U) (hlU : (La bm p ws l a').length + p + 1 ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (aPassW R Pay Dg) σ (outAt σ Dg (R 34) (La bm p ws l a')) (aPB U) := by
  have h17 := hz 17 (by decide)
  have h25 := hz 25 (by decide)
  have h38 := hz 38 (by decide)
  have h39 := hz 39 (by decide)
  have d1 := Hash4.wcopyR_spec cap (R 1) (R 17) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) σ h17 h39 (by omega)
  rw [hG] at d1
  have d2 := WExec.inc (cap := cap) (R 25) (σ.setv (R 17) G) (by simp [h25]; omega)
  rw [show (σ.setv (R 17) G).val (R 25) + 1 = 1 by simp [h25]] at d2
  have d3 := Hash4.wcopyR_spec cap (R 0) (R 38) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((σ.setv (R 17) G).setv (R 25) 1) (by simp [h38]) (by simp [h39])
    (by simp [hA]; omega)
  rw [show ((σ.setv (R 17) G).setv (R 25) 1).val (R 0) = a' by simp [hA]] at d3
  have e3 : ((σ.setv (R 17) G).setv (R 25) 1).setv (R 38) a' = acSt R σ Dg a' G bm p m ws l 0 := by
    unfold acSt; simp only [Gs, Bs, La, Nat.sub_zero]
    rw [outAt_self _ _ _ _ (by simp [hlst]) (by simp [hlsh]) (by simp [hlw])]
  rw [e3] at d3
  have d4 := circ_spec cap (R 38) (fun i => cBodyAW R (Pay i) Dg) a' (cAB U) ha (by omega)
    (acSt R σ Dg a' G bm p m ws l) (fun k _ => by simp [acSt, outAt])
    (aStep_spec cap R Pay Dg hPD a' cD S m zs ws rest G p bm U l σ hst hs hc hzs hws hm hp hbm hP h23
      (Zs_sub R _ _ _ (by decide) hz) hcU hmU hGU hlU hU)
  have hBa := Bs_lt bm p hp a'
  have d5 := wclear_spec cap (R 25) (Bs bm p a') (acSt R σ Dg a' G bm p m ws l a') (by simp [acSt, outAt])
    (by simp [acSt, outAt]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 d5)))) ?_ (by unfold aPB; omega)
  unfold acSt
  rw [← outAt_setv _ _ _ _ (R 25) (R.injective.ne (by decide)), hGa, Nat.sub_self]
  congr 1
  refine WState.eq rfl rfl ?_ rfl
  funext y
  simp only [WState.setv_val, Function.update_apply]
  by_cases y1 : y = R 25
  · rw [y1]; simp [h25]
  by_cases y2 : y = R 38
  · rw [y2]; simp [h38]
  by_cases y3 : y = R 17
  · rw [y3]; simp [h17]
  simp [y1, y2, y3]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
