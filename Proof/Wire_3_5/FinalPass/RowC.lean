import Proof.Wire_3_5.FinalPass.RowB

/-! # `RowW`, part 3: one circuit's target term (P3:2585-2592)

`tBodyW`: to the selected child, over its `S` weights (`skipsW`), `V := (t mod p).toNat` for its target, `a := B · V
mod p`, `T := (T + a) mod p` in `R 41` (with `R 42 = p − T`), back to the start, `B := B · base mod p`, `S` cleared.
Main declarations: `tCost`, **`tBody_spec`**. Paper quantity: circuit `i`'s term `base^i · t_i` of `L_g`'s target,
modulo `p` (the residue `r₀ = (−target) mod p` of row `(g, p)`). -/

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

/-- One circuit's target term. -/
def tBodyW (E : Fin (ns + 1)) : WM ns nr :=
  .seq (navW R E) (.seq (Hash4.wcopyR (R 15) (R 19) (R 39)) (.seq (skipsW R E) (.seq (modW2W E (R 14) (Rg R) false)
    (.seq (Hash4.wcopyR (R 2) (R 27) (R 39)) (.seq (mulLoopW (mlW R)) (.seq (WM.clear (R 27))
    (.seq (addLoopW (R 41) (R 42) (R 26)) (.seq (rew2W E (R 14)) (.seq (bUpdW R) (WM.clear (R 15)))))))))))

/-- One circuit's target term's step bound. -/
def tCost (S m g nz Lm p J : ℕ) : ℕ :=
  navCost S m g nz Lm + 1 + (18 * S + 3 + 1 + ((S * (24 * Lm + 23) + 1) + 1 + (modCost2 Lm p + 1 +
    (18 * p + 3 + 1 + (p * ThrArith.mulStep p + 1 + 1 + (3 * p + 1 + 1 + (p * (7 * p + 12) + 1 + 1 +
    ((7 * J + 3) + 1 + (bUpdCost p + 1 + (3 * S + 1))))))))))

theorem tBody_spec (E : Fin (ns + 1)) (S m g : ℕ) (zs ws : List ℤ) (t : ℤ) (c rest : List Bool)
    (p B bm T U : ℕ) (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 0)
    (hc : c = natWord S ++ (natWord m ++ (zs.flatMap intWord ++ (ws.flatMap intWord ++ (intWord t ++ rest)))))
    (hzs : zs.length = g % m * (S + 1)) (hws : ws.length = S) (hm : 1 ≤ m) (hp : 1 ≤ p) (hB : B < p)
    (hbm : bm < p) (hT : T < p) (hg : σ.val (R 17) = g) (hBv : σ.val (R 25) = B) (hbmv : σ.val (R 23) = bm)
    (hP : σ.val (R 2) = p) (h41 : σ.val (R 41) = T) (h42 : σ.val (R 42) = p - T) (hz : Zs R σ cL)
    (hcU : c.length ≤ U) (hmU : m ≤ U) (hgU : g ≤ U) (hpU : p ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (tBodyW R E) σ
      ((((σ.setv (R 17) (g / m)).setv (R 25) (B * bm % p)).setv (R 41) ((T + B * (t % (p : ℤ)).toNat % p) % p)).setv
        (R 42) (p - (T + B * (t % (p : ℤ)).toNat % p) % p))
      (tCost S m g zs.length c.length p ((natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
        (ws.flatMap intWord).length + (intWord t).length)) := by
  have hpos : 0 < p := by omega
  have hPc := Rg_ne_Pc R
  have hlen : c.length = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length +
      (ws.flatMap intWord).length + (intWord t).length + rest.length := by rw [hc]; simp only [List.length_append]; ring
  have hzl := fm_len_ge zs
  have hwl := fm_len_ge ws
  have htl := ThrCore.intWord_length' t
  have h15 := hz 15 (by decide)
  have h19 := hz 19 (by decide)
  have h26 := hz 26 (by decide)
  have h27 := hz 27 (by decide)
  have h39 := hz 39 (by decide)
  have h40 := hz 40 (by decide)
  obtain ⟨J1, hJ1⟩ : ∃ J, J = (natWord S).length + (natWord m).length + (zs.flatMap intWord).length := ⟨_, rfl⟩
  obtain ⟨τ0, hτ0⟩ : ∃ τ, τ = (σ.setv (R 15) S).setv (R 17) (g / m) := ⟨_, rfl⟩
  have hτ5 : τ0.val (R 5) = 0 := by rw [hτ0]; simp [hz 5 (by decide)]
  have hτ14 : τ0.val (R 14) = 0 := by rw [hτ0]; simp [hz 14 (by decide)]
  have hτ19 : τ0.val (R 19) = 0 := by rw [hτ0]; simp [h19]
  have hτ26 : τ0.val (R 26) = 0 := by rw [hτ0]; simp [h26]
  have hτ27 : τ0.val (R 27) = 0 := by rw [hτ0]; simp [h27]
  have hτsh : τ0.sh E = 0 := by rw [hτ0]; simp [hs]
  -- to the selected child
  have d1 := nav_spec cap R E S m g zs c.length (fun z hz' => le_trans (nbl_le_fm zs z hz') (by omega)) c
    (ws.flatMap intWord ++ (intWord t ++ rest)) σ hst hs hc hzs (Zs_sub R _ _ _ (by decide) hz) hg hm (by omega)
    (by omega) (by omega) (by omega) (by omega)
  rw [← hJ1, ← hτ0] at d1
  -- over the weights
  have d2 := Hash4.wcopyR_spec cap (R 15) (R 19) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (at2 τ0 E (R 14) J1) (by simp [at2, hτ0, h19]) (by simp [at2, hτ0, h39])
    (by simp [at2, hτ0]; omega)
  rw [show (at2 τ0 E (R 14) J1).val (R 15) = S by simp [at2, hτ0]] at d2
  have d3 := skips_spec cap R E ws c.length (fun z hz' => le_trans (nbl_le_fm ws z hz') (by omega)) c
    (intWord t ++ rest) J1 ((at2 τ0 E (R 14) J1).setv (R 19) S) (by simp [at2, hτ0, hst]) (by simp [at2])
    (by simp [at2]) (by rw [hc, hJ1, ← List.append_assoc, ← List.append_assoc, List.drop_left' (by simp; ring)])
    (by simp [hws]) (by simp [at2, hτ0, hz 7 (by decide)]) (by omega) (by omega)
  obtain ⟨J2, hJ2⟩ : ∃ J, J = J1 + (ws.flatMap intWord).length := ⟨_, rfl⟩
  rw [← hJ2] at d3
  have e3 : at2 (((at2 τ0 E (R 14) J1).setv (R 19) S).setv (R 19) 0) E (R 14) J2 = at2 τ0 E (R 14) J2 := by
    clear d1 d2 d3 hz hτ0
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y0 : y = R 19
      · rw [y0]; simp_all [at2, Function.update_apply]
      by_cases y1 : y = R 14
      · rw [y1]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e3] at d3
  -- the target's residue
  have hzτ : Zs R τ0 coreL := by
    rw [hτ0]
    exact Zs_setv R _ _ _ _ (by decide) (Zs_setv R _ _ _ _ (by decide) (Zs_sub R _ _ _ (by decide) hz))
  have d4 := modW2_spec cap E (R 14) (Rg R) hPc false t c rest J2 p hp (by omega) (at2 τ0 E (R 14) J2)
    (by simp [at2, hτ0, hst]) (by simp [at2]) (by simp [at2])
    (by rw [hc, hJ2, hJ1, ← List.append_assoc, ← List.append_assoc, ← List.append_assoc,
      List.drop_left' (by simp; ring)])
    (by simp [at2, hτ0, hP]) (core_zero R _ (Zs_at2 R _ _ _ _ (by decide) hzτ)) (by omega)
  obtain ⟨V, hVe⟩ : ∃ V, V = (t % (p : ℤ)).toNat := ⟨_, rfl⟩
  have hV : V < p := by
    have h1 : t % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hpos)
    have h2 : 0 ≤ t % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
    omega
  obtain ⟨J3, hJ3⟩ : ∃ J, J = J2 + (intWord t).length := ⟨_, rfl⟩
  rw [show (if false = true then -t else t) = t from rfl, ← hVe, ← hJ3, Rg1] at d4
  have e4 : at2 ((at2 τ0 E (R 14) J2).setv (R 5) V) E (R 14) J3 = at2 (τ0.setv (R 5) V) E (R 14) J3 := by
    clear d1 d2 d3 d4 hz e3 hτ0
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y0 : y = R 5
      · rw [y0]; simp_all [at2, Function.update_apply]
      by_cases y1 : y = R 14
      · rw [y1]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e4] at d4
  -- the product and the sum
  have d5 := Hash4.wcopyR_spec cap (R 2) (R 27) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (at2 (τ0.setv (R 5) V) E (R 14) J3) (by simp [at2, hτ0, h27])
    (by simp [at2, hτ0, h39]) (by simp [at2, hτ0, hP]; omega)
  rw [show (at2 (τ0.setv (R 5) V) E (R 14) J3).val (R 2) = p by simp [at2, hτ0, hP]] at d5
  have d6 := mulLoop_spec cap (mlW R) p B (by omega) hB V ((at2 (τ0.setv (R 5) V) E (R 14) J3).setv (R 27) p) 0
    (by simp [at2]) (by omega) (by simp [at2, hτ0, h26]) hpos (by simp) (by simp [at2, hτ0, hBv])
    (by simp [at2, hτ0, h39]) (by simp [at2, hτ0, h40])
  obtain ⟨a, ha⟩ : ∃ a, a = (0 + B * V) % p := ⟨_, rfl⟩
  rw [← ha] at d6
  simp only [mlW0, mlW1, mlW2] at d6
  have hap : a < p := by rw [ha]; exact Nat.mod_lt _ hpos
  have e6 : ((((at2 (τ0.setv (R 5) V) E (R 14) J3).setv (R 27) p).setv (R 5) 0).setv (R 26) a).setv (R 27) (p - a) =
      at2 ((τ0.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J3 := by
    clear d1 d2 d3 d4 d5 d6 hz e3 e4 hτ0
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y0 : y = R 5
      · rw [y0]; simp_all [at2, Function.update_apply]
      by_cases y1 : y = R 26
      · rw [y1]; simp_all [at2, Function.update_apply]
      by_cases y2 : y = R 27
      · rw [y2]; simp_all [at2, Function.update_apply]
      by_cases y3 : y = R 14
      · rw [y3]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e6] at d6
  have d7 := wclear_spec cap (R 27) (p - a) (at2 ((τ0.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J3)
    (by simp [at2]) (by simp [at2]; omega)
  have e7 : (at2 ((τ0.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J3).setv (R 27) 0 =
      at2 (τ0.setv (R 26) a) E (R 14) J3 := by
    clear d1 d2 d3 d4 d5 d6 d7 hz e3 e4 e6 hτ0
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y0 : y = R 26
      · rw [y0]; simp_all [at2, Function.update_apply]
      by_cases y1 : y = R 27
      · rw [y1]; simp_all [at2, Function.update_apply]
      by_cases y2 : y = R 14
      · rw [y2]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e7] at d7
  have d8 := addLoop_spec cap (R 41) (R 42) (R 26) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) p (by omega) a (at2 (τ0.setv (R 26) a) E (R 14) J3) T (by simp [at2])
    (by omega) (by simp [at2, hτ0, h41]) (by simp [at2, hτ0, h42]) hT
  obtain ⟨T', hT'⟩ : ∃ x, x = (T + a) % p := ⟨_, rfl⟩
  rw [← hT'] at d8
  have e8 : (((at2 (τ0.setv (R 26) a) E (R 14) J3).setv (R 41) T').setv (R 42) (p - T')).setv (R 26) 0 =
      at2 ((τ0.setv (R 41) T').setv (R 42) (p - T')) E (R 14) J3 := by
    clear d1 d2 d3 d4 d5 d6 d7 d8 hz e3 e4 e6 e7 hτ0
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y0 : y = R 26
      · rw [y0]; simp_all [at2, Function.update_apply]
      by_cases y1 : y = R 41
      · rw [y1]; simp_all [at2, Function.update_apply]
      by_cases y2 : y = R 42
      · rw [y2]; simp_all [at2, Function.update_apply]
      by_cases y3 : y = R 14
      · rw [y3]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e8] at d8
  -- back, the next power, S cleared
  have d9 := rew2_spec cap E (R 14) J3 (at2 ((τ0.setv (R 41) T').setv (R 42) (p - T')) E (R 14) J3)
    (by simp [at2]) (by omega) (by simp [at2])
  have e9 : ((at2 ((τ0.setv (R 41) T').setv (R 42) (p - T')) E (R 14) J3).setv (R 14) 0).seth E 0 =
      (τ0.setv (R 41) T').setv (R 42) (p - T') := by
    clear d1 d2 d3 d4 d5 d6 d7 d8 d9 hz e3 e4 e6 e7 e8 hτ0
    refine WState.eq ?_ ?_ ?_ ?_
    · wst_sh
    · wst_st
    · funext y
      by_cases y0 : y = R 14
      · rw [y0]; simp_all [at2, Function.update_apply]
      by_cases y1 : y = R 41
      · rw [y1]; simp_all [at2, Function.update_apply]
      by_cases y2 : y = R 42
      · rw [y2]; simp_all [at2, Function.update_apply]
      simp_all [at2, Function.update_apply]
    · rfl
  rw [e9] at d9
  have d10 := bUpd_spec cap R p bm B (by omega) hbm hB ((τ0.setv (R 41) T').setv (R 42) (p - T'))
    (by simp [hτ0, hP]) (by simp [hτ0, hbmv]) (by simp [hτ0, hBv]) (by simp [hτ0, h26]) (by simp [hτ0, h27])
    (by simp [hτ0, hz 28 (by decide)]) (by simp [hτ0, h39]) (by simp [hτ0, h40])
  have d11 := wclear_spec cap (R 15) S (((τ0.setv (R 41) T').setv (R 42) (p - T')).setv (R 25) (B * bm % p))
    (by simp [hτ0]) (by simp [hτ0]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6
    (WExec.seq d7 (WExec.seq d8 (WExec.seq d9 (WExec.seq d10 d11)))))))))) ?_ (by
    unfold tCost
    have m1 : (ws.flatMap intWord).length ≥ 0 := Nat.zero_le _
    have m2 : V * ThrArith.mulStep p ≤ p * ThrArith.mulStep p := Nat.mul_le_mul_right _ hV.le
    have m3 : a * (7 * p + 12) ≤ p * (7 * p + 12) := Nat.mul_le_mul_right _ hap.le
    have m4 := modCost2_le (natBitLength t.natAbs) p c.length p (by omega) le_rfl
    rw [hws] at d3 ⊢
    omega)
  rw [show B * (t % (p : ℤ)).toNat % p = a by rw [ha, ← hVe, Nat.zero_add], ← hT', hτ0]
  clear d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 hz e3 e4 e6 e7 e8 e9
  refine WState.eq rfl rfl ?_ rfl
  funext y
  by_cases y1 : y = R 15
  · rw [y1]; simp_all [Function.update_apply]
  by_cases y2 : y = R 17
  · rw [y2]; simp_all [Function.update_apply]
  by_cases y3 : y = R 25
  · rw [y3]; simp_all [Function.update_apply]
  by_cases y4 : y = R 41
  · rw [y4]; simp_all [Function.update_apply]
  by_cases y5 : y = R 42
  · rw [y5]; simp_all [Function.update_apply]
  simp_all [Function.update_apply]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
