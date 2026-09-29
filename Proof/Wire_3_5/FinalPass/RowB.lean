import Proof.Wire_3_5.FinalPass.RowA

/-! # `RowW`, part 2: one circuit's coefficients; one circuit's target term (P3:2585-2592)

`cBodyAW`: to the selected child, its `S` coefficients appended in unary (`aWeightsW`), back to the start, the next
power. `tBodyW`: to the selected child, over its weights (`skipsW`), its target's residue times the power added
into `R 41` modulo `p` (`R 42 = p − R 41`), back to the start, the next power. Main declarations: `cACost`,
**`cBodyA_spec`**, `tCost`, **`tBody_spec`**. Paper quantities: circuit `i`'s block of the reduced coefficients
`a_i`, and its term `base^i · t_i` of the target of `L_g`, modulo `p`. -/

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

/-- One circuit's coefficients. -/
def cBodyAW (E Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (navW R E) (.seq (Hash4.wcopyR (R 15) (R 20) (R 39)) (.seq (aWeightsW R E Dg) (.seq (rew2W E (R 14))
    (.seq (bUpdW R) (WM.clear (R 15))))))

/-- One circuit's coefficients' step bound. -/
def cACost (S m g nz Lm p J : ℕ) : ℕ :=
  navCost S m g nz Lm + 1 + (18 * S + 3 + 1 + ((S * (aCost Lm p + 4) + 1) + 1 + ((7 * J + 3) + 1 +
    (bUpdCost p + 1 + (3 * S + 1)))))

theorem cBodyA_spec (E Dg : Fin (ns + 1)) (hED : E ≠ Dg) (S m g : ℕ) (zs ws : List ℤ) (c rest : List Bool)
    (p B bm U : ℕ) (l : List Bool) (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 0)
    (hc : c = natWord S ++ (natWord m ++ (zs.flatMap intWord ++ (ws.flatMap intWord ++ rest))))
    (hzs : zs.length = g % m * (S + 1)) (hws : ws.length = S) (hm : 1 ≤ m) (hp : 1 ≤ p) (hB : B < p)
    (hbm : bm < p) (hlst : σ.st Dg = l) (hlsh : σ.sh Dg = l.length) (hlw : σ.val (R 34) = l.length)
    (hg : σ.val (R 17) = g) (hBv : σ.val (R 25) = B) (hbmv : σ.val (R 23) = bm) (hP : σ.val (R 2) = p)
    (hz : Zs R σ cL) (hcU : c.length ≤ U) (hmU : m ≤ U) (hgU : g ≤ U)
    (hlU : (l ++ aWord B p ws).length + p + 1 ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (cBodyAW R E Dg) σ
      (outAt ((σ.setv (R 17) (g / m)).setv (R 25) (B * bm % p)) Dg (R 34) (l ++ aWord B p ws))
      (cACost S m g zs.length c.length p ((natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
        (ws.flatMap intWord).length)) := by
  have hlen : c.length = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
      (ws.flatMap intWord).length + rest.length := by rw [hc]; simp only [List.length_append]; ring
  have hzl := fm_len_ge zs
  have hwl := fm_len_ge ws
  have h15 := hz 15 (by decide)
  have h20 := hz 20 (by decide)
  have h39 := hz 39 (by decide)
  obtain ⟨J1, hJ1⟩ : ∃ J, J = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length := ⟨_, rfl⟩
  have d1 := nav_spec cap R E S m g zs c.length (fun z hz' => le_trans (nbl_le_fm zs z hz') (by omega)) c
    (ws.flatMap intWord ++ rest) σ hst hs hc hzs (Zs_sub R _ _ _ (by decide) hz) hg hm (by omega) (by omega)
    (by omega) (by omega) (by omega)
  rw [← hJ1] at d1
  have d2 := Hash4.wcopyR_spec cap (R 15) (R 20) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1)
    (by simp [at2, h20]) (by simp [at2, h39]) (by simp [at2]; omega)
  have e2 : (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).setv (R 20)
      ((at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).val (R 15)) =
      aSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E Dg J1 l S := by
    unfold aSt; clear d1 d2 hz; wst_eq
  rw [e2, show (at2 ((σ.setv (R 15) S).setv (R 17) (g / m)) E (R 14) J1).val (R 15) = S by simp [at2]] at d2
  have d3 := aWeights_spec cap R E Dg hED ws c.length (fun w hw => le_trans (nbl_le_fm ws w hw) (by omega)) c rest J1
    p B l hp (by omega) hB ((σ.setv (R 15) S).setv (R 17) (g / m)) (by simp [hst])
    (by rw [hc, hJ1, ← List.append_assoc, ← List.append_assoc, List.drop_left' (by simp; ring)])
    (by simp [hP]) (by simp [hBv]) (Zs_setv R _ _ _ _ (by decide)
      (Zs_setv R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz))) (by omega) (by omega) (by omega)
  rw [hws] at d3
  have d4 := rew2_spec cap E (R 14) (J1 + (ws.flatMap intWord).length)
    (aSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E Dg (J1 + (ws.flatMap intWord).length) (l ++ aWord B p ws) 0)
    (by simp [aSt, at2, outAt]) (by omega) (by simp [aSt, at2])
  have e4 : ((aSt R ((σ.setv (R 15) S).setv (R 17) (g / m)) E Dg (J1 + (ws.flatMap intWord).length)
      (l ++ aWord B p ws) 0).setv (R 14) 0).seth E 0 =
      outAt ((σ.setv (R 15) S).setv (R 17) (g / m)) Dg (R 34) (l ++ aWord B p ws) := by
    have h14 := hz 14 (by decide)
    unfold aSt; clear d1 d2 d3 hz e2; wst_eq
  rw [e4] at d4
  have d5 := bUpd_spec cap R p bm B (by omega) hbm hB
    (outAt ((σ.setv (R 15) S).setv (R 17) (g / m)) Dg (R 34) (l ++ aWord B p ws))
    (by simp [outAt, hP]) (by simp [outAt, hbmv]) (by simp [outAt, hBv]) (by simp [outAt, hz 26 (by decide)])
    (by simp [outAt, hz 27 (by decide)]) (by simp [outAt, hz 28 (by decide)]) (by simp [outAt, h39])
    (by simp [outAt, hz 40 (by decide)])
  have d6 := wclear_spec cap (R 15) S ((outAt ((σ.setv (R 15) S).setv (R 17) (g / m)) Dg (R 34)
    (l ++ aWord B p ws)).setv (R 25) (B * bm % p)) (by simp [outAt]) (by simp [outAt]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_ (by
    unfold cACost; omega)
  clear d1 d2 d3 d4 d5 d6 e2 e4 hz
  refine WState.eq ?_ ?_ ?_ ?_
  · wst_sh
  · wst_st
  · funext x
    by_cases x1 : x = R 15
    · rw [x1]; simp_all [outAt, Function.update_apply]
    by_cases x2 : x = R 17
    · rw [x2]; simp_all [outAt, Function.update_apply]
    by_cases x4 : x = R 34
    · rw [x4]; simp_all [outAt, Function.update_apply]
    by_cases x5 : x = R 25
    · rw [x5]; simp_all [outAt, Function.update_apply]
    simp_all [outAt, Function.update_apply]
  · rfl

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
