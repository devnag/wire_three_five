import Proof.Wire_3_5.FinalPass.ThrRead5

/-! # FRAMED payloads, part 6: one natural number exactly (`natWord v` → `V = v`)

(P3:2543-2551, W17.) A payload starts with `natWord |supp|` and `natWord |children|`. `natW2W` counts the
length `L` into `Ln`, steps over the separator, sets `W := 1`, folds the `L` digits exactly (`bitNLoopW`: `A += W` on a
`1`, `W := 2W`), moves `A` into `V` and clears `W`. The capacity must hold `2^L ≤ 2v + 2` (`pow_nbl_le`). Main
declarations: `pow_nbl_le`, `natCost`, **`natW2_spec`**. Paper quantities: `|supp_i|`, `|children_i|`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

theorem pow_nbl_le (v : ℕ) : 2 ^ natBitLength v ≤ 2 * v + 2 := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos v with h | h
  · subst h; simp
  · have := Nat.pow_log_le_self 2 (Nat.pos_iff_ne_zero.mp h)
    rw [pow_succ]; omega

theorem natWord_length' (v : ℕ) : (RepairRepresentation.natWord v).length = 2 * natBitLength v + 1 := by
  rw [natWord_split, List.length_append, List.length_replicate, List.length_cons, fixed_length]; ring

/-- `natW2W`'s step bound. -/
def natCost (v : ℕ) : ℕ :=
  13 * natBitLength v + 28 + natBitLength v * (50 * (2 * v + 2) + 24) + 7 * v + 3 * (2 * v + 2)

variable {ns nr : ℕ} (cap : ℕ) (E : Fin (ns + 1)) (Pc : Fin nr) (Rg : Fin 10 ↪ Fin nr)

/-- **One natural number, exactly**: `V := v` from `natWord v` at the framed head. -/
def natW2W : WM ns nr :=
  .seq (cnt2W E Pc (Rg 3)) (.seq (adv2W E Pc) (.seq (.inc (Rg 6)) (.seq (bitNLoopW E Pc Rg)
    (.seq (WM.move (Rg 4) (Rg 1)) (WM.clear (Rg 6))))))

theorem natW2_spec (hPc : ∀ i, Rg i ≠ Pc) (v : ℕ) (c rest : List Bool) (j : ℕ) (σ : WState ns nr)
    (hst : σ.st E = frame c) (hs : σ.sh E = 2 * j + 1) (hp : σ.val Pc = j)
    (hd : c.drop j = RepairRepresentation.natWord v ++ rest) (hz : ∀ i : Fin 10, i ≠ 0 → σ.val (Rg i) = 0)
    (hjc : j + (RepairRepresentation.natWord v).length ≤ cap) (hvc : 2 * v + 2 ≤ cap) :
    WExec cap (natW2W E Pc Rg) σ (at2 (σ.setv (Rg 1) v) E Pc (j + (RepairRepresentation.natWord v).length))
      (natCost v) := by
  have vv : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => rne Rg h
  have hlen := natWord_length' v
  have hpw := pow_nbl_le v
  have hd1 : c.drop j = List.replicate (natBitLength v) true ++ false ::
      (WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v ++ rest) := by
    rw [hd, natWord_split]; simp
  -- the length
  have d1 := cnt2_spec cap E Pc (Rg 3) (Ne.symm (hPc 3)) c
    (WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v ++ rest) (natBitLength v) σ j 0 hst hs hp hd1
    (hz 3 (by decide)) (by omega) (by omega)
  obtain ⟨σ1, e1⟩ : ∃ τ, τ = at2 (σ.setv (Rg 3) (0 + natBitLength v)) E Pc (j + natBitLength v) := ⟨_, rfl⟩
  rw [← e1] at d1
  have d2 := adv2_spec cap E Pc σ1 (j + natBitLength v) (by rw [e1, at2_sh_E]) (by rw [e1, at2_val_Pc])
    (by omega)
  obtain ⟨σ2, e2⟩ : ∃ τ, τ = at2 σ1 E Pc (j + natBitLength v + 1) := ⟨_, rfl⟩
  rw [← e2] at d2
  have g2 : ∀ i : Fin 10, i ≠ 3 → σ2.val (Rg i) = σ.val (Rg i) := fun i h3 => by
    rw [e2, at2_val_ne _ _ _ _ _ (hPc i), e1, at2_val_ne _ _ _ _ _ (hPc i)]
    simp [Function.update_apply, vv i 3 h3]
  have d3 := WExec.inc (cap := cap) (Rg 6) σ2 (by rw [g2 6 (by decide), hz 6 (by decide)]; omega)
  rw [g2 6 (by decide), hz 6 (by decide), Nat.zero_add] at d3
  obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setv (Rg 6) 1 := ⟨_, rfl⟩
  rw [← e3] at d3
  have g3 : ∀ i : Fin 10, i ≠ 6 → σ3.val (Rg i) = σ2.val (Rg i) := fun i h6 => by
    rw [e3]; simp [Function.update_apply, vv i 6 h6]
  have s3 : σ3.st = σ.st ∧ σ3.sh E = 2 * (j + natBitLength v + 1) + 1 ∧ σ3.val Pc = j + natBitLength v + 1 := by
    rw [e3, e2, e1]
    refine ⟨rfl, by simp [at2], ?_⟩
    simp [Function.update_apply, Ne.symm (hPc 6), at2]
  -- the digits
  have hbits : c.drop (j + natBitLength v + 1) = WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v ++ rest := by
    rw [show j + natBitLength v + 1 = j + (natBitLength v + 1) by ring, ← List.drop_drop, hd1]
    simp [List.drop_append]
  have hbv := bval_natWord v
  have d4 := bitNLoop_spec cap E Pc Rg hPc c rest (2 * v + 2) hvc
    (WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v) σ3 0 1 (j + natBitLength v + 1)
    (by rw [s3.1, hst]) s3.2.1 s3.2.2 hbits (by rw [fixed_length]; omega)
    (by rw [g3 3 (by decide), e2, at2_val_ne _ _ _ _ _ (hPc 3), e1, at2_val_ne _ _ _ _ _ (hPc 3), fixed_length]; simp)
    (by rw [fixed_length]; omega) (by rw [g3 4 (by decide), g2 4 (by decide), hz 4 (by decide)])
    (by rw [e3]; simp) (by rw [hbv]; omega) (by rw [fixed_length]; omega)
    (by rw [g3 8 (by decide), g2 8 (by decide), hz 8 (by decide)])
    (by rw [g3 9 (by decide), g2 9 (by decide), hz 9 (by decide)])
  obtain ⟨σ4, e4⟩ : ∃ τ, τ = at2 (nSt Rg σ3 0 1 (WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v)) E Pc
      (j + natBitLength v + 1 + (WilliamsPublishedForm.fixedWidthNatBits (natBitLength v) v).length) := ⟨_, rfl⟩
  rw [← e4] at d4
  have a4 : σ4.val (Rg 4) = v := by rw [e4, at2_val_ne _ _ _ _ _ (hPc 4)]; simp [nSt, hbv]
  have a1 : σ4.val (Rg 1) = 0 := by
    rw [e4, at2_val_ne _ _ _ _ _ (hPc 1)]
    simp [nSt, vv 1 4 (by decide), vv 1 6 (by decide), vv 1 3 (by decide), g3 1 (by decide), g2 1 (by decide),
      hz 1 (by decide)]
  have a6 : σ4.val (Rg 6) = 2 ^ natBitLength v := by
    rw [e4, at2_val_ne _ _ _ _ _ (hPc 6)]; simp [nSt, vv 6 4 (by decide), fixed_length]
  -- the result
  have d5 := wmove_spec cap (Rg 4) (Rg 1) (vv 4 1 (by decide)) v σ4 a4 (by omega) (by omega)
  rw [a1, a4, Nat.zero_add] at d5
  have d6 := wclear_spec cap (Rg 6) (2 ^ natBitLength v) ((σ4.setv (Rg 4) 0).setv (Rg 1) v)
    (by simp [Function.update_apply, vv 6 1 (by decide), vv 6 4 (by decide), a6])
    (by simp [Function.update_apply, vv 6 1 (by decide), vv 6 4 (by decide), a6]; omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 (WExec.seq d4 (WExec.seq d5 d6))))) ?_
    (by unfold natCost; rw [fixed_length]; nlinarith)
  rw [e4, hlen]
  apply WState.eq
  · funext i; by_cases hi : i = E
    · rw [hi]; simp [at2, fixed_length]; ring
    · simp only [WState.setv_sh]
      rw [at2_sh_ne _ _ _ _ _ hi, at2_sh_ne _ _ _ _ _ hi]
      show σ3.sh i = σ.sh i
      rw [e3, e2, e1]; simp [at2, Function.update_apply, hi]
  · show σ3.st = σ.st
    exact s3.1
  · funext r
    by_cases hr : r = Pc
    · rw [hr]
      simp only [WState.setv_val, Function.update_apply, if_neg (Ne.symm (hPc 6)), if_neg (Ne.symm (hPc 1)),
        if_neg (Ne.symm (hPc 4))]
      rw [at2_val_Pc, at2_val_Pc, fixed_length]; ring
    · simp only [WState.setv_val, Function.update_apply]
      rw [at2_val_ne (σ.setv (Rg 1) v) E Pc _ r hr]
      by_cases h6 : r = Rg 6
      · rw [if_pos h6, h6, WState.setv_val, Function.update_apply, if_neg (vv 6 1 (by decide)), hz 6 (by decide)]
      · rw [if_neg h6]
        by_cases h1 : r = Rg 1
        · rw [if_pos h1, h1]; simp
        · rw [if_neg h1]
          by_cases h4 : r = Rg 4
          · rw [if_pos h4, h4, WState.setv_val, Function.update_apply, if_neg (vv 4 1 (by decide)),
              hz 4 (by decide)]
          · rw [if_neg h4, at2_val_ne _ _ _ _ _ hr]
            simp only [nSt, if_neg h4, if_neg h6, WState.setv_val, Function.update_apply, if_neg h1]
            by_cases h3 : r = Rg 3
            · rw [if_pos h3, h3, hz 3 (by decide)]
            · rw [if_neg h3, e3]
              simp only [WState.setv_val, Function.update_apply, if_neg h6]
              rw [e2, at2_val_ne _ _ _ _ _ hr, e1, at2_val_ne _ _ _ _ _ hr]
              simp [Function.update_apply, h3]
  · show σ3.cell = σ.cell
    rw [e3, e2, e1]; rfl

end NearCubicWires.WireExponent3_5.FinalPass.ThrRead
