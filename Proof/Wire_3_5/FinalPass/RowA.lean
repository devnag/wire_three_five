import Proof.Wire_3_5.FinalPass.DigsFinal

/-! # `RowW`, part 1: stage 8's row word, one reduced coefficient (P3:2585-2592)

Stage 8 reads row `(g, p)` as `rowWord p r₀ as ws` (`Term.rowWord`: `1^p 0`, `1^{r₀} 0`, one `1^{a_i} 0` per occurrence,
the digit section, a final `0`). `unW` appends `1^X 0`; `aBodyW` reads one weight `w`, forms `a = (B · (w mod p))
mod p` and appends `1^a 0`; `aWeightsW` does it for a circuit's selected child's weights. Main declarations: `unW`,
`unW_spec`, `aBody_spec`, `aSt`, **`aWeights_spec`**. Paper quantity: the reduced coefficients `a_i = w_i mod p` of
row `(g, p)`. -/

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

/-- Append `1^X 0`, `X` counted down. -/
def unW (Dg : Fin (ns + 1)) (Lw X : Fin nr) : WM ns nr := .seq (onesW Dg Lw X) (emitBitW Dg Lw false)

theorem unW_spec (Dg : Fin (ns + 1)) (Lw X : Fin nr) (hXL : X ≠ Lw) (k : ℕ) (σ : WState ns nr) (l : List Bool)
    (hX : σ.val X = k) (hst : σ.st Dg = l) (hsh : σ.sh Dg = l.length) (hlw : σ.val Lw = l.length)
    (hc : l.length + k + 1 ≤ cap) :
    WExec cap (unW Dg Lw X) σ (outAt (σ.setv X 0) Dg Lw (l ++ ListEval.unary k)) (11 * k + 9) := by
  have d1 := ones_spec cap Dg Lw X hXL k σ l hX (by omega) hst hsh hlw (by omega)
  have d2 := emitBit_spec cap Dg Lw false (outAt (σ.setv X 0) Dg Lw (l ++ List.replicate k true))
    (l ++ List.replicate k true) (outAt_st_Dg _ _ _ _) (outAt_sh_Dg _ _ _ _) (outAt_val_Lw _ _ _ _) (by simp; omega)
  refine WExec.cast cap (WExec.seq d1 d2) ?_ (by omega)
  rw [outAt_outAt, List.append_assoc]; rfl

/-- One weight's coefficient: its residue, times the power, appended in unary. -/
def aBodyW (E Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (modW2W E (R 14) (Rg R) false) (.seq (Hash4.wcopyR (R 2) (R 27) (R 39)) (.seq (mulLoopW (mlW R))
    (.seq (WM.clear (R 27)) (unW Dg (R 34) (R 26)))))

/-- One coefficient's zero registers. -/
def aL : List (Fin digsK) := [5, 6, 7, 8, 9, 10, 11, 12, 13, 26, 27, 39, 40]

/-- One coefficient's step bound. -/
def aCost (L p : ℕ) : ℕ :=
  modCost2 L p + 1 + (18 * p + 3 + 1 + (p * ThrArith.mulStep p + 1 + 1 + (3 * p + 1 + 1 + (11 * p + 9))))

theorem aBody_spec (E Dg : Fin (ns + 1)) (hED : E ≠ Dg) (w : ℤ) (c rest : List Bool) (j p B : ℕ)
    (l : List Bool) (hp : 1 ≤ p) (hpc : p ≤ cap) (hB : B < p) (σ : WState ns nr) (hst : σ.st E = frame c)
    (hs : σ.sh E = 2 * j + 1) (hpj : σ.val (R 14) = j) (hd : c.drop j = intWord w ++ rest)
    (hP : σ.val (R 2) = p) (hBv : σ.val (R 25) = B) (hlst : σ.st Dg = l) (hlsh : σ.sh Dg = l.length)
    (hlw : σ.val (R 34) = l.length) (hz : Zs R σ aL) (hjc : j + (intWord w).length ≤ cap)
    (hlc : l.length + p + 1 ≤ cap) :
    WExec cap (aBodyW R E Dg) σ
      (at2 (outAt σ Dg (R 34) (l ++ ListEval.unary (B * (w % (p : ℤ)).toNat % p))) E (R 14) (j + (intWord w).length))
      (aCost (natBitLength w.natAbs) p) := by
  have hPc := Rg_ne_Pc R
  have hpos : 0 < p := by omega
  obtain ⟨V, hVe⟩ : ∃ V, V = (w % (p : ℤ)).toNat := ⟨_, rfl⟩
  have hV : V < p := by
    have h1 : w % (p : ℤ) < p := Int.emod_lt_of_pos _ (by exact_mod_cast hpos)
    have h2 : 0 ≤ w % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hpos.ne')
    omega
  have h26 := hz 26 (by decide)
  have h27 := hz 27 (by decide)
  have h39 := hz 39 (by decide)
  have h40 := hz 40 (by decide)
  obtain ⟨J, hJ⟩ : ∃ J, J = j + (intWord w).length := ⟨_, rfl⟩
  have d1 := modW2_spec cap E (R 14) (Rg R) hPc false w c rest j p hp hpc σ hst hs hpj hd (by simp [hP])
    (core_zero R _ (Zs_sub R _ _ _ (by decide) hz)) hjc
  rw [show (if false = true then -w else w) = w from rfl, ← hVe, ← hJ, Rg1] at d1
  have d2 := Hash4.wcopyR_spec cap (R 2) (R 27) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) (at2 (σ.setv (R 5) V) E (R 14) J)
    (by simp [at2, h27]) (by simp [at2, h39]) (by simp [at2, hP]; omega)
  have e2 : (at2 (σ.setv (R 5) V) E (R 14) J).setv (R 27) ((at2 (σ.setv (R 5) V) E (R 14) J).val (R 2)) =
      at2 ((σ.setv (R 5) V).setv (R 27) p) E (R 14) J := by
    clear d1 d2 hz; wst_eq
  rw [e2, show (at2 (σ.setv (R 5) V) E (R 14) J).val (R 2) = p by simp [at2, hP]] at d2
  have d3 := mulLoop_spec cap (mlW R) p B hpc hB V (at2 ((σ.setv (R 5) V).setv (R 27) p) E (R 14) J) 0
    (by simp [at2]) (by omega) (by simp [at2, h26]) hpos (by simp [at2]) (by simp [at2, hBv])
    (by simp [at2, h39]) (by simp [at2, h40])
  obtain ⟨a, ha⟩ : ∃ a, a = (0 + B * V) % p := ⟨_, rfl⟩
  rw [← ha] at d3
  simp only [mlW0, mlW1, mlW2] at d3
  have hap : a < p := by rw [ha]; exact Nat.mod_lt _ hpos
  have e3 : (((at2 ((σ.setv (R 5) V).setv (R 27) p) E (R 14) J).setv (R 5) 0).setv (R 26) a).setv (R 27) (p - a) =
      at2 ((σ.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J := by
    have h5 := hz 5 (by decide)
    clear d1 d2 d3 hz e2; wst_eq
  rw [e3] at d3
  have d4 := wclear_spec cap (R 27) (p - a) (at2 ((σ.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J)
    (by simp [at2]) (by simp [at2]; omega)
  have e4 : (at2 ((σ.setv (R 26) a).setv (R 27) (p - a)) E (R 14) J).setv (R 27) 0 = at2 (σ.setv (R 26) a) E (R 14) J := by
    clear d1 d2 d3 d4 hz e2 e3; wst_eq
  rw [e4] at d4
  have d5 := unW_spec cap Dg (R 34) (R 26) (R.injective.ne (by decide)) a (at2 (σ.setv (R 26) a) E (R 14) J) l
    (by simp [at2]) (by simp [at2, hED.symm, hlst]) (by simp [at2, hED.symm, hlsh]) (by simp [at2, hlw]) (by omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 d5)))) ?_ (by
    unfold aCost
    have : V * ThrArith.mulStep p ≤ p * ThrArith.mulStep p := Nat.mul_le_mul_right _ hV.le
    omega)
  rw [show B * (w % (p : ℤ)).toNat % p = a by rw [ha, ← hVe, Nat.zero_add], ← hJ]
  clear d1 d2 d3 d4 d5 hz e2 e3 e4
  refine WState.eq ?_ ?_ ?_ ?_
  · wst_sh
  · wst_st
  · funext y
    by_cases y1 : y = R 26
    · rw [y1]; simp_all [at2, outAt, Function.update_apply]
    by_cases y2 : y = R 34
    · rw [y2]; simp_all [at2, outAt, Function.update_apply]
    by_cases y3 : y = R 14
    · rw [y3]; simp_all [at2, outAt, Function.update_apply]
    simp_all [at2, outAt, Function.update_apply]
  · rfl

/-- The coefficients' loop state: reading position `j`, output `l`, countdown `k`. -/
def aSt (τ : WState ns nr) (E Dg : Fin (ns + 1)) (j : ℕ) (l : List Bool) (k : ℕ) : WState ns nr :=
  at2 (outAt (τ.setv (R 20) k) Dg (R 34) l) E (R 14) j

theorem aSt_setv20 (τ : WState ns nr) (E Dg : Fin (ns + 1)) (j : ℕ) (l : List Bool) (k v : ℕ) :
    (aSt R τ E Dg j l k).setv (R 20) v = aSt R τ E Dg j l v := by
  unfold aSt; wst_eq

/-- The words appended for a circuit's weights at power `B`. -/
def aWord (B p : ℕ) (ws : List ℤ) : List Bool := (ws.map fun w => B * (w % (p : ℤ)).toNat % p).flatMap ListEval.unary

theorem aWord_take (B p : ℕ) (ws : List ℤ) (k : ℕ) (hk : k < ws.length) :
    aWord B p (ws.take (k + 1)) = aWord B p (ws.take k) ++ ListEval.unary (B * (ws[k] % (p : ℤ)).toNat % p) := by
  unfold aWord
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.flatMap_append]
  simp

/-- A circuit's coefficients. -/
def aWeightsW (E Dg : Fin (ns + 1)) : WM ns nr := countW (R 20) (aBodyW R E Dg)

theorem aWeights_spec (E Dg : Fin (ns + 1)) (hED : E ≠ Dg) (ws : List ℤ) (Lm : ℕ)
    (hLm : ∀ w ∈ ws, natBitLength w.natAbs ≤ Lm) (c rest : List Bool) (j0 p B : ℕ) (l : List Bool)
    (hp : 1 ≤ p) (hpc : p ≤ cap) (hB : B < p) (τ : WState ns nr) (hst : τ.st E = frame c)
    (hd : c.drop j0 = ws.flatMap intWord ++ rest) (hP : τ.val (R 2) = p) (hBv : τ.val (R 25) = B)
    (hz : Zs R τ aL) (hjc : j0 + (ws.flatMap intWord).length ≤ cap) (hn : ws.length ≤ cap)
    (hlc : (l ++ aWord B p ws).length + p + 1 ≤ cap) :
    WExec cap (aWeightsW R E Dg) (aSt R τ E Dg j0 l ws.length)
      (aSt R τ E Dg (j0 + (ws.flatMap intWord).length) (l ++ aWord B p ws) 0)
      (ws.length * (aCost Lm p + 4) + 1) := by
  have hF := count_spec cap (R 20) (aBodyW R E Dg) ws.length (aCost Lm p) hn
    (fun k => aSt R τ E Dg (j0 + ((ws.take k).flatMap intWord).length) (l ++ aWord B p (ws.take k)) (ws.length - k))
    (fun k _ => by simp [aSt, at2, outAt])
    (fun k hk => by
      have hsplit := fm_split ws k
      have hdk := fm_drop ws k hk
      have htk := fm_take ws k hk
      have hlen : ((ws.take k).flatMap intWord).length + (intWord ws[k]).length ≤ (ws.flatMap intWord).length := by
        rw [hsplit, hdk]; simp
      have hat := aWord_take B p ws k hk
      have hpre : (l ++ aWord B p (ws.take (k + 1))).length ≤ (l ++ aWord B p ws).length := by
        have e : aWord B p ws = aWord B p (ws.take (k + 1)) ++ aWord B p (ws.drop (k + 1)) := by
          unfold aWord; rw [← List.flatMap_append, ← List.map_append, List.take_append_drop]
        rw [e]; simp only [List.length_append]; omega
      rw [aSt_setv20]
      have dx := aBody_spec cap R E Dg hED ws[k] c ((ws.drop (k + 1)).flatMap intWord ++ rest)
        (j0 + ((ws.take k).flatMap intWord).length) p B (l ++ aWord B p (ws.take k)) hp hpc hB
        (aSt R τ E Dg (j0 + ((ws.take k).flatMap intWord).length) (l ++ aWord B p (ws.take k)) (ws.length - k - 1))
        (by simp [aSt, at2, outAt, hst, Function.update_apply, hED]) (by simp [aSt, at2]) (by simp [aSt, at2])
        (by rw [← List.drop_drop, hd, hsplit, List.append_assoc, List.drop_left, hdk, List.append_assoc])
        (by simp [aSt, at2, outAt, hP]) (by simp [aSt, at2, outAt, hBv])
        (by simp [aSt, at2, outAt, Function.update_apply, hED.symm])
        (by simp [aSt, at2, outAt, Function.update_apply, hED.symm]) (by simp [aSt, at2, outAt])
        (fun r hr => by
          have h20 : r ≠ 20 := by rintro rfl; revert hr; decide
          have h34 : r ≠ 34 := by rintro rfl; revert hr; decide
          have h14 : r ≠ 14 := by rintro rfl; revert hr; decide
          have := hz r hr
          simp [aSt, at2, outAt, Function.update_apply, R.injective.ne h20, R.injective.ne h34, R.injective.ne h14,
            this])
        (by omega) (by rw [hat] at hpre; simp at hpre hlc ⊢; omega)
      refine WExec.cast cap dx ?_ (by
        have h1 := hLm ws[k] (List.getElem_mem hk)
        have := modCost2_le (natBitLength ws[k].natAbs) p Lm p h1 le_rfl
        unfold aCost; omega)
      rw [show ws.length - (k + 1) = ws.length - k - 1 by omega, htk, hat, ← Nat.add_assoc, ← List.append_assoc]
      unfold aSt
      clear dx hz hsplit hdk htk hlen hat hpre
      refine WState.eq ?_ ?_ ?_ ?_
      · wst_sh
      · wst_st
      · funext y
        by_cases y1 : y = R 20
        · rw [y1]; simp_all [at2, outAt, Function.update_apply]
        by_cases y2 : y = R 34
        · rw [y2]; simp_all [at2, outAt, Function.update_apply]
        by_cases y3 : y = R 14
        · rw [y3]; simp_all [at2, outAt, Function.update_apply]
        simp_all [at2, outAt, Function.update_apply]
      · rfl)
  have e0 : aSt R τ E Dg (j0 + ((ws.take 0).flatMap intWord).length) (l ++ aWord B p (ws.take 0)) (ws.length - 0) =
      aSt R τ E Dg j0 l ws.length := by simp [aWord]
  rw [e0, Nat.sub_self, List.take_length] at hF
  exact hF

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
