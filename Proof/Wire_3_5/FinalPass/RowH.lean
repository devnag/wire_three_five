import Proof.Wire_3_5.FinalPass.RowG

/-! # `RowW`, part 8: the row program, second half (P3:2596-2599)

`rowBW`: `W := 1`, `R 44 := p − 1`, `R 35 := τ₀`, the digit weights (`dwLoopW`), `R 43`, `R 44` cleared, the final
`false`, the output rewound by its length. From `outAt σ Dg Lw L` (all non-input registers zero) it leaves exactly
`σ.sets Dg (L ++ digWord (weights) ++ [false])`. Main declarations: `setv3_back`, `rowBW`, `rowBB`, **`rowB_spec`**.
Paper quantity: the digit section `2^d mod p`, `d < τ₀`, of row `(g, p)`'s word. -/

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

theorem setv3_init {ns nr : ℕ} (s : WState ns nr) (a b c : Fin nr) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y z w : ℕ) : (((s.setv a x).setv b y).setv b z).setv c w = ((s.setv c w).setv a x).setv b z := by
  refine WState.eq rfl rfl ?_ rfl
  funext v
  simp only [WState.setv_val, Function.update_apply]
  by_cases h1 : v = a
  · subst h1; simp [hab, hac]
  by_cases h2 : v = b
  · subst h2; simp [Ne.symm hab, hbc]
  by_cases h3 : v = c
  · subst h3; simp [Ne.symm hac, Ne.symm hbc]
  simp [h1, h2, h3]

theorem setv3_back {ns nr : ℕ} (s : WState ns nr) (a b c : Fin nr) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (x y : ℕ) (ha : s.val a = 0) (hb : s.val b = 0) (hc : s.val c = 0) :
    ((((s.setv a 0).setv b x).setv c y).setv b 0).setv c 0 = s := by
  refine WState.eq rfl rfl ?_ rfl
  funext v
  simp only [WState.setv_val, Function.update_apply]
  by_cases h1 : v = a
  · subst h1; simp [hab, hac, ha]
  by_cases h2 : v = b
  · subst h2; simp [Ne.symm hab, hbc, hb]
  by_cases h3 : v = c
  · subst h3; simp [Ne.symm hac, Ne.symm hbc, hc]
  simp [h1, h2, h3]

variable {ns nr : ℕ} (cap : ℕ) (R : Fin digsK ↪ Fin nr)

/-- The row program's second half. -/
def rowBW (Dg : Fin (ns + 1)) : WM ns nr :=
  .seq (.inc (R 43)) (.seq (Hash4.wcopyR (R 2) (R 44) (R 39)) (.seq (.dec (R 44)) (.seq (Hash4.wcopyR (R 3) (R 35) (R 39))
    (.seq (dwLoopW R Dg) (.seq (WM.clear (R 43)) (.seq (WM.clear (R 44)) (.seq (emitBitW Dg (R 34) false)
    (WM.rewind Dg (R 34)))))))))

/-- The second half's bound. -/
def rowBB (U : ℕ) : ℕ :=
  3 + 1 + (18 * U + 3 + 1 + (1 + 1 + (18 * U + 3 + 1 + ((U * (dwCost U + 4) + 1) + 1 + ((3 * U + 1) + 1 +
    ((3 * U + 1) + 1 + (7 + 1 + (5 * U + 1))))))))

theorem dwCost_le (p U : ℕ) (h : p ≤ U) : dwCost p ≤ dwCost U := by unfold dwCost; gcongr

theorem rowB_spec (Dg : Fin (ns + 1)) (p τ U : ℕ) (hp : 2 ≤ p) (σ : WState ns nr) (L : List Bool)
    (hDh : σ.sh Dg = 0) (hP : σ.val (R 2) = p) (hT : σ.val (R 3) = τ) (hz : Zs R σ allL)
    (hpU : p ≤ U) (hτU : τ ≤ U)
    (hlU : L.length + τ * (p + 1) + p + 2 ≤ U) (hU : 2 * U + 2 ≤ cap) :
    WExec cap (rowBW R Dg) (outAt σ Dg (R 34) L)
      (σ.sets Dg (L ++ Term.digWord ((List.range τ).map fun d => 2 ^ d % p) ++ [false])) (rowBB U) := by
  have h33 := hz 33 (by decide)
  have h34 := hz 34 (by decide)
  have h35 := hz 35 (by decide)
  have h39 := hz 39 (by decide)
  have h40 := hz 40 (by decide)
  have h43 := hz 43 (by decide)
  have h44 := hz 44 (by decide)
  have hlen := digWord_len_le p (by omega) τ
  have d1 := WExec.inc (cap := cap) (R 43) (outAt σ Dg (R 34) L) (by simp [outAt, h43]; omega)
  rw [show (outAt σ Dg (R 34) L).val (R 43) + 1 = 1 by simp [outAt, h43]] at d1
  have d2 := Hash4.wcopyR_spec cap (R 2) (R 44) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((outAt σ Dg (R 34) L).setv (R 43) 1) (by simp [outAt, h44]) (by simp [outAt, h39])
    (by simp [outAt, hP]; omega)
  rw [show ((outAt σ Dg (R 34) L).setv (R 43) 1).val (R 2) = p by simp [outAt, hP]] at d2
  have d3 := WExec.dec (cap := cap) (R 44) (((outAt σ Dg (R 34) L).setv (R 43) 1).setv (R 44) p) (by simp; omega)
  rw [show (((outAt σ Dg (R 34) L).setv (R 43) 1).setv (R 44) p).val (R 44) - 1 = p - 1 by simp] at d3
  have d4 := Hash4.wcopyR_spec cap (R 3) (R 35) (R 39) (R.injective.ne (by decide)) (R.injective.ne (by decide))
    (R.injective.ne (by decide)) ((((outAt σ Dg (R 34) L).setv (R 43) 1).setv (R 44) p).setv (R 44) (p - 1))
    (by simp [outAt, h35]) (by simp [outAt, h39]) (by simp [outAt, hT]; omega)
  rw [show ((((outAt σ Dg (R 34) L).setv (R 43) 1).setv (R 44) p).setv (R 44) (p - 1)).val (R 3) = τ by
    simp [outAt, hT]] at d4
  have e4 : ((((outAt σ Dg (R 34) L).setv (R 43) 1).setv (R 44) p).setv (R 44) (p - 1)).setv (R 35) τ =
      dwSt R σ Dg τ p L 0 := by
    unfold dwSt
    rw [← outAt_setv _ _ _ _ (R 43) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 44) (R.injective.ne (by decide)),
      ← outAt_setv _ _ _ _ (R 44) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 35) (R.injective.ne (by decide)),
      setv3_init σ (R 43) (R 44) (R 35) (R.injective.ne (by decide)) (R.injective.ne (by decide))
        (R.injective.ne (by decide))]
    simp only [Nat.sub_zero, pow_zero, Nat.mod_eq_of_lt (show 1 < p by omega), List.range_zero, List.map_nil,
      Term.digWord, List.flatMap_nil, List.append_nil]
  rw [e4] at d4
  have d5 := dwLoop_spec cap R Dg τ p hp (by omega) (by omega) σ L h33 h39 h40 (by omega)
  have hWm : 2 ^ τ % p < p := Nat.mod_lt _ (by omega)
  have d6 := wclear_spec cap (R 43) (2 ^ τ % p) (dwSt R σ Dg τ p L τ) (by simp [dwSt, outAt]) (by simp [dwSt, outAt]; omega)
  have d7 := wclear_spec cap (R 44) (p - 2 ^ τ % p) ((dwSt R σ Dg τ p L τ).setv (R 43) 0) (by simp [dwSt, outAt])
    (by simp [dwSt, outAt]; omega)
  have e7 : ((dwSt R σ Dg τ p L τ).setv (R 43) 0).setv (R 44) 0 =
      outAt σ Dg (R 34) (L ++ Term.digWord ((List.range τ).map fun d => 2 ^ d % p)) := by
    unfold dwSt
    rw [← outAt_setv _ _ _ _ (R 43) (R.injective.ne (by decide)), ← outAt_setv _ _ _ _ (R 44) (R.injective.ne (by decide)),
      Nat.sub_self, setv3_back σ (R 35) (R 43) (R 44) (R.injective.ne (by decide)) (R.injective.ne (by decide))
      (R.injective.ne (by decide)) _ _ h35 h43 h44]
  rw [e7] at d7
  have d8 := emitBit_spec cap Dg (R 34) false (outAt σ Dg (R 34) (L ++ Term.digWord ((List.range τ).map fun d =>
    2 ^ d % p))) (L ++ Term.digWord ((List.range τ).map fun d => 2 ^ d % p)) (outAt_st_Dg _ _ _ _)
    (outAt_sh_Dg _ _ _ _) (outAt_val_Lw _ _ _ _) (by simp only [List.length_append]; nlinarith)
  rw [outAt_outAt] at d8
  have d9 := wrewind_spec cap Dg (R 34) (L ++ Term.digWord ((List.range τ).map fun d => 2 ^ d % p) ++ [false]).length
    (outAt σ Dg (R 34) (L ++ Term.digWord ((List.range τ).map fun d => 2 ^ d % p) ++ [false])) (outAt_val_Lw _ _ _ _)
    (by simp only [outAt_val_Lw, List.length_append, List.length_singleton]; nlinarith)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 (WExec.seq d6
    (WExec.seq d7 (WExec.seq d8 d9)))))))) ?_ (by
    unfold rowBB
    have h1 : τ * (dwCost p + 4) ≤ U * (dwCost U + 4) := Nat.mul_le_mul hτU (by have := dwCost_le p U hpU; omega)
    have h2 : (L ++ Term.digWord ((List.range τ).map fun d => 2 ^ d % p) ++ [false]).length ≤ U := by
      simp only [List.length_append, List.length_singleton]; nlinarith
    omega)
  refine WState.eq ?_ ?_ ?_ rfl
  · funext i; by_cases hi : i = Dg
    · rw [hi]; simp [outAt, hDh]
    · simp [outAt, Function.update_apply, hi]
  · funext i; by_cases hi : i = Dg
    · rw [hi]; simp [outAt]
    · simp [outAt, Function.update_apply, hi]
  · funext y; by_cases hy : y = R 34
    · rw [hy]; simp [outAt, h34]
    · simp [outAt, Function.update_apply, hy]

end NearCubicWires.WireExponent3_5.FinalPass.DigsBody
