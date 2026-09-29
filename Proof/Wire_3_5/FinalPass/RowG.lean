import Proof.Wire_3_5.FinalPass.RowF

/-! # `RowW`, part 7: the row program, first half (P3:2585-2599)

`rowAW`: the base pass (`R 23 = base mod p`), the target pass (`R 41 = T`), `1^p 0`, `1^{(p − T) mod p} 0`, `R 41`,
`R 42` cleared, the coefficient pass, `R 23`, `R 24` cleared. From the entry (inputs in `R 0 … R 4`, other registers
zero, output blank) it leaves only the output `unary p ++ unary r₀ ++ coefficients`. Main declarations: `rowAW`,
`rowAB`, **`rowA_spec`**. Paper quantities: `p`, `r₀` and the reduced coefficients `a_i` of row `(g, p)`. -/

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

theorem setv2_back {ns nr : ℕ} (s : WState ns nr) (a b : Fin nr) (hab : a ≠ b) (x y : ℕ) (ha : s.val a = 0)
    (hb : s.val b = 0) : (((s.setv a x).setv b y).setv a 0).setv b 0 = s := by
  refine WState.eq rfl rfl ?_ rfl
  funext z
  simp only [WState.setv_val, Function.update_apply]
  by_cases h1 : z = a
  · subst h1; simp [hab, ha]
  by_cases h2 : z = b
  · subst h2; simp [Ne.symm hab, hb]
  simp [h1, h2]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The row program's first half. -/
def rowAW (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (baseW R Pay) (.seq (tPassW R Pay) (.seq (unPW R Dg) (.seq (unR0W R Dg) (.seq (WM.clear (R 41))
    (.seq (WM.clear (R 42)) (.seq (aPassW R Pay Dg) (.seq (WM.clear (R 23)) (WM.clear (R 24)))))))))

/-- The first half's bound. -/
def rowAB (U : ℕ) : ℕ :=
  bB U + 1 + (tPB U + 1 + ((18 * U + 3 + 1 + (11 * U + 9)) + 1 + ((18 * U + 3 + 1 + (11 * U + 9) + 1) + 1 +
    ((3 * U + 1) + 1 + ((3 * U + 1) + 1 + (aPB U + 1 + ((3 * U + 1) + 1 + (3 * U + 1))))))))

theorem rowA_spec (Pay : Fin 4 → Fin (ns + 1)) (Dg : Fin (ns + 1)) (hPD : ∀ i, Pay i ≠ Dg) (a' : ℕ) (ha : a' ≤ 4)
    (cD : ℕ → List Bool) (S m : ℕ → ℕ) (zs ws : ℕ → List ℤ) (t : ℕ → ℤ) (rest : ℕ → List Bool)
    (G p U : ℕ) (σ : WState ns nr)
    (hst : ∀ i : Fin 4, i.val < a' → σ.st (Pay i) = frame (cD i.val))
    (hs : ∀ i : Fin 4, i.val < a' → σ.sh (Pay i) = 0)
    (hc : ∀ i, i < a' → cD i = natWord (S i) ++ (natWord (m i) ++ ((zs i).flatMap intWord ++
      ((ws i ++ [t i]).flatMap intWord ++ rest i))))
    (hzs : ∀ i, i < a' → (zs i).length = Gs G m i % m i * (S i + 1)) (hws : ∀ i, i < a' → (ws i).length = S i)
    (hm : ∀ i, i < a' → 1 ≤ m i) (hGa : Gs G m a' = 0) (hp : 2 ≤ p)
    (hDs : σ.st Dg = []) (hDh : σ.sh Dg = 0)
    (hA : σ.val (R 0) = a') (hG : σ.val (R 1) = G) (hP : σ.val (R 2) = p) (hz : Zs R σ allL)
    (hcU : ∀ i, i < a' → (cD i).length ≤ U) (hmU : ∀ i, i < a' → m i ≤ U) (hGU : G ≤ U) (hpU : p ≤ U)
    (hlU : (La (Bf p (fun i => ws i ++ [t i]) a') p ws (ListEval.unary p ++
      ListEval.unary ((p - Tf (Bf p (fun i => ws i ++ [t i]) a') p t a') % p)) a').length + p + 1 ≤ U)
    (haU : a' ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (rowAW R Pay Dg) σ (outAt σ Dg (R 34) (La (Bf p (fun i => ws i ++ [t i]) a') p ws (ListEval.unary p ++
      ListEval.unary ((p - Tf (Bf p (fun i => ws i ++ [t i]) a') p t a') % p)) a')) (rowAB U) := by
  obtain ⟨bm, hbm⟩ : ∃ b, b = Bf p (fun i => ws i ++ [t i]) a' := ⟨_, rfl⟩
  rw [← hbm] at hlU ⊢
  have hbmp : bm < p := by rw [hbm]; exact Bf_lt p hp _ a'
  obtain ⟨T, hTd⟩ : ∃ T, T = Tf bm p t a' := ⟨_, rfl⟩
  rw [← hTd] at hlU ⊢
  have hTp : T < p := by rw [hTd]; exact Tf_lt bm p (by omega) t a'
  have h23z := hz 23 (by decide)
  have h24z := hz 24 (by decide)
  have h33 := hz 33 (by decide)
  have h34 := hz 34 (by decide)
  have h39 := hz 39 (by decide)
  have h41z := hz 41 (by decide)
  have h42z := hz 42 (by decide)
  -- the base
  have d1 := base_spec cap R Pay a' ha cD S m zs (fun i => ws i ++ [t i]) rest G p U σ hst hs hc hzs
    (fun i hi => by simp [hws i hi]) hm hGa hp hA hG hP (Zs_sub R _ _ _ (by decide) hz) hcU hmU hGU hpU haU hU
  rw [← hbm] at d1
  obtain ⟨S1, hS1⟩ : ∃ s, s = (σ.setv (R 23) bm).setv (R 24) (p - bm) := ⟨_, rfl⟩
  rw [← hS1] at d1
  -- the target
  have d2 := tPass_spec cap R Pay a' ha cD S m zs ws t rest G p bm U S1 (fun i hi => by rw [hS1]; simp [hst i hi])
    (fun i hi => by rw [hS1]; simp [hs i hi]) (fun i hi => by rw [hc i hi]; simp [List.flatMap_append]) hzs hws hm hGa
    hp hbmp (by rw [hS1]; simp [hA]) (by rw [hS1]; simp [hG]) (by rw [hS1]; simp [hP]) (by rw [hS1]; simp)
    (by rw [hS1]; exact Zs_setv R _ _ _ _ (by decide) (Zs_setv R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz)))
    hcU hmU hGU hpU haU hU
  rw [← hTd] at d2
  obtain ⟨S2, hS2⟩ : ∃ s, s = (S1.setv (R 41) T).setv (R 42) (p - T) := ⟨_, rfl⟩
  rw [← hS2] at d2
  have e2 : S2.st Dg = [] ∧ S2.sh Dg = 0 ∧ S2.val (R 34) = 0 ∧ S2.val (R 33) = 0 ∧ S2.val (R 39) = 0 ∧
      S2.val (R 2) = p ∧ S2.val (R 41) = T ∧ S2.val (R 42) = p - T := by
    rw [hS2, hS1]; refine ⟨by simp [hDs], by simp [hDh], ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [h34, h33, h39, hP]
  -- 1^p 0, 1^{r₀} 0
  have d3 := unP_spec cap R Dg p S2 [] e2.2.2.2.2.2.1 e2.1 e2.2.1 e2.2.2.1 e2.2.2.2.1 e2.2.2.2.2.1 (by simp; omega)
  have d4 := unR0_spec cap R Dg p T hTp (outAt S2 Dg (R 34) ([] ++ ListEval.unary p)) ([] ++ ListEval.unary p)
    (by simp [outAt, e2.2.2.2.2.2.2.1]) (by simp [outAt, e2.2.2.2.2.2.2.2]) (outAt_st_Dg _ _ _ _) (outAt_sh_Dg _ _ _ _)
    (outAt_val_Lw _ _ _ _) (by simp [outAt, e2.2.2.2.1]) (by simp [outAt, e2.2.2.2.2.1])
    (by have := La_mono bm p ws (ListEval.unary p ++ ListEval.unary ((p - T) % p)) 0 a' (Nat.zero_le _)
        simp [La, ListEval.unary] at this hlU ⊢; omega)
  rw [outAt_outAt, List.nil_append] at d4
  -- clear T
  have d5 := wclear_spec cap (R 41) T (outAt S2 Dg (R 34) (ListEval.unary p ++ ListEval.unary ((p - T) % p)))
    (by simp [outAt, e2.2.2.2.2.2.2.1]) (by simp [outAt, e2.2.2.2.2.2.2.1]; omega)
  have d6 := wclear_spec cap (R 42) (p - T)
    ((outAt S2 Dg (R 34) (ListEval.unary p ++ ListEval.unary ((p - T) % p))).setv (R 41) 0)
    (by simp [outAt, e2.2.2.2.2.2.2.2]) (by simp [outAt, e2.2.2.2.2.2.2.2]; omega)
  have e6 : ((outAt S2 Dg (R 34) (ListEval.unary p ++ ListEval.unary ((p - T) % p))).setv (R 41) 0).setv (R 42) 0 =
      outAt S1 Dg (R 34) (ListEval.unary p ++ ListEval.unary ((p - T) % p)) := by
    rw [← outAt_setv _ _ _ _ (R 41) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 42) (R.injective.ne (by decide)),
      hS2, setv2_back S1 (R 41) (R 42) (R.injective.ne (by decide)) T (p - T) (by rw [hS1]; simp [h41z])
        (by rw [hS1]; simp [h42z])]
  rw [e6] at d6
  -- the coefficients
  have d7 := aPass_spec cap R Pay Dg hPD a' ha cD S m zs ws (fun i => intWord (t i) ++ rest i) G p bm U
    (ListEval.unary p ++ ListEval.unary ((p - T) % p)) (outAt S1 Dg (R 34) (ListEval.unary p ++
      ListEval.unary ((p - T) % p)))
    (fun i hi => by simp [outAt, Function.update_apply, hPD i, hS1, hst i hi])
    (fun i hi => by simp [outAt, Function.update_apply, hPD i, hS1, hs i hi])
    (fun i hi => by rw [hc i hi]; simp [List.flatMap_append]) hzs hws hm hGa hp hbmp (outAt_st_Dg _ _ _ _)
    (outAt_sh_Dg _ _ _ _) (outAt_val_Lw _ _ _ _) (by simp [outAt, hS1, hA]) (by simp [outAt, hS1, hG])
    (by simp [outAt, hS1, hP]) (by simp [outAt, hS1])
    (fun r hr => by
      have r34 : r ≠ 34 := by rintro rfl; revert hr; decide
      have r23 : r ≠ 23 := by rintro rfl; revert hr; decide
      have r24 : r ≠ 24 := by rintro rfl; revert hr; decide
      have := hz r (by revert hr; revert r; decide)
      simp [outAt, hS1, Function.update_apply, R.injective.ne r34, R.injective.ne r23, R.injective.ne r24, this])
    hcU hmU hGU hpU haU hlU hU
  rw [outAt_outAt] at d7
  -- clear the base
  have d8 := wclear_spec cap (R 23) bm (outAt S1 Dg (R 34) (La bm p ws (ListEval.unary p ++
    ListEval.unary ((p - T) % p)) a')) (by simp [outAt, hS1]) (by simp [outAt, hS1]; omega)
  have d9 := wclear_spec cap (R 24) (p - bm) ((outAt S1 Dg (R 34) (La bm p ws (ListEval.unary p ++
    ListEval.unary ((p - T) % p)) a')).setv (R 23) 0) (by simp [outAt, hS1]) (by simp [outAt, hS1]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6
    (WExec.seq d7 (WExec.seq d8 d9)))))))) ?_ (by unfold rowAB; omega)
  rw [← outAt_setv _ _ _ _ (R 23) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 24) (R.injective.ne (by decide)),
    hS1, setv2_back σ (R 23) (R 24) (R.injective.ne (by decide)) bm (p - bm) h23z h24z]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
