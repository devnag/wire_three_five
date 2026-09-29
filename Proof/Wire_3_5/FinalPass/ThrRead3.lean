import Proof.Wire_3_5.FinalPass.ThrRead2

/-! # The THR residues from FRAMED payloads, part 3: one integer's residue, signed or absolute

(P3:2585-2623, W17.) `core2W` (sign, length, digits) followed by `ThrCore.tailW` gives
`V = (z mod p).toNat` (`modW2_spec`, the reduced coefficient of a weight); followed by `absTailW` it gives
`V = |z| mod p` (`absW2_spec`, a term of the stack base `1 + Σ ‖child_i‖`). Both leave every other register as it
was and the head past `intWord z`. Main declarations: `coreSt`, `core2_spec`, **`modW2_spec`**, **`absW2_spec`**.
Paper quantities: `w mod p` and `|w| mod p` for the numbers of the selected children. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

variable {ns nr : ℕ} (cap : ℕ) (E : Fin (ns + 1)) (Pc : Fin nr) (Rg : Fin 10 ↪ Fin nr)

/-- Sign, length, digits. -/
def core2W : WM ns nr := .seq (head2W E Pc Rg) (.seq (initW Rg) (bitLoop2W E Pc Rg))

/-- The registers after `core2W`: `A = a`, `D = p − a`, `W = w`, `WD = p − w`, `Ln = 0`, `S = s`. -/
def coreSt (σ : WState ns nr) (p s a w : ℕ) : WState ns nr :=
  ⟨σ.sh, σ.st,
    fun r => if r = Rg 4 then a else if r = Rg 5 then p - a else if r = Rg 6 then w else if r = Rg 7 then p - w
      else if r = Rg 3 then 0 else if r = Rg 2 then s else σ.val r, σ.cell⟩

/-- `core2W`'s step bound. -/
def coreCost (L p : ℕ) : ℕ := 13 * L + 22 + 1 + (43 * p + 16 + 1 + (L * (bitCost2 p + 2) + 1))

theorem core2_spec (hPc : ∀ i, Rg i ≠ Pc) (z : ℤ) (c rest : List Bool) (j p : ℕ) (hp : 1 ≤ p) (hpc : p ≤ cap)
    (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 2 * j + 1) (hpj : σ.val Pc = j)
    (hd : c.drop j = RepairRepresentation.intWord z ++ rest) (hP : σ.val (Rg 0) = p)
    (hz : ∀ i : Fin 10, i ≠ 0 → σ.val (Rg i) = 0) (hjc : j + (RepairRepresentation.intWord z).length ≤ cap) :
    WExec cap (core2W E Pc Rg) σ
      (at2 (coreSt Rg σ p (decide (z < 0)).toNat (z.natAbs % p) (1 % p * 2 ^ natBitLength z.natAbs % p)) E Pc
        (j + (RepairRepresentation.intWord z).length)) (coreCost (natBitLength z.natAbs) p) := by
  have hpos : 0 < p := by omega
  have v : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => rne Rg h
  have hlen := intWord_length' z
  -- head
  have d1 := head2_spec cap E Pc Rg hPc z c rest j σ hst hs hpj hd (hz 2 (by decide)) (hz 3 (by decide))
    (by omega)
  obtain ⟨σA, eA⟩ : ∃ τ, τ = at2 ((σ.setv (Rg 2) (decide (z < 0)).toNat).setv (Rg 3) (natBitLength z.natAbs)) E Pc
      (j + 2 + natBitLength z.natAbs) := ⟨_, rfl⟩
  rw [← eA] at d1
  have gA : ∀ i : Fin 10, i ≠ 2 → i ≠ 3 → σA.val (Rg i) = σ.val (Rg i) := fun i h2 h3 => by
    rw [eA, at2_val_ne _ _ _ _ _ (hPc i)]; simp [Function.update_apply, v i 2 h2, v i 3 h3]
  -- init
  have d2 := init_spec cap Rg p hp hpc σA (by rw [gA 0 (by decide) (by decide), hP])
    (by rw [gA 5 (by decide) (by decide), hz 5 (by decide)]) (by rw [gA 6 (by decide) (by decide), hz 6 (by decide)])
    (by rw [gA 7 (by decide) (by decide), hz 7 (by decide)]) (by rw [gA 9 (by decide) (by decide), hz 9 (by decide)])
  obtain ⟨σB, eB⟩ : ∃ τ, τ = (((σA.setv (Rg 5) p).setv (Rg 7) p).setv (Rg 6) (1 % p)).setv (Rg 7) (p - 1 % p) :=
    ⟨_, rfl⟩
  rw [← eB] at d2
  have gB : ∀ i : Fin 10, i ≠ 5 → i ≠ 6 → i ≠ 7 → σB.val (Rg i) = σA.val (Rg i) := fun i h5 h6 h7 => by
    rw [eB]; simp [Function.update_apply, v i 5 h5, v i 6 h6, v i 7 h7]
  have sB : σB.st = σ.st ∧ σB.sh E = 2 * (j + 2 + natBitLength z.natAbs) + 1 ∧
      σB.val Pc = j + 2 + natBitLength z.natAbs ∧ σB.cell = σ.cell := by
    rw [eB, eA]
    refine ⟨rfl, by simp [at2], ?_, rfl⟩
    simp [Function.update_apply, Ne.symm (hPc 5), Ne.symm (hPc 6), Ne.symm (hPc 7), at2]
  -- digits
  have hbits : c.drop (j + 2 + natBitLength z.natAbs) =
      WilliamsPublishedForm.fixedWidthNatBits (natBitLength z.natAbs) z.natAbs ++ rest := by
    rw [show j + 2 + natBitLength z.natAbs = j + (2 + natBitLength z.natAbs) by ring, ← List.drop_drop, hd,
      drop_intWord]
  have d3 := bitLoop2_spec cap E Pc Rg hPc p hp hpc c rest
    (WilliamsPublishedForm.fixedWidthNatBits (natBitLength z.natAbs) z.natAbs) σB 0 (1 % p)
    (j + 2 + natBitLength z.natAbs) (by rw [sB.1, hst]) sB.2.1 sB.2.2.1 hbits (by rw [fixed_length]; omega)
    (by rw [gB 3 (by decide) (by decide) (by decide), eA, at2_val_ne _ _ _ _ _ (hPc 3), fixed_length]; simp)
    (by rw [fixed_length]; omega)
    (by rw [gB 4 (by decide) (by decide) (by decide), gA 4 (by decide) (by decide), hz 4 (by decide)])
    (by rw [eB]; simp [Function.update_apply, v 5 7 (by decide), v 5 6 (by decide)]) hpos
    (by rw [eB]; simp [Function.update_apply, v 6 7 (by decide)])
    (by rw [eB]; simp) (Nat.mod_lt _ hpos)
    (by rw [gB 8 (by decide) (by decide) (by decide), gA 8 (by decide) (by decide), hz 8 (by decide)])
    (by rw [gB 9 (by decide) (by decide) (by decide), gA 9 (by decide) (by decide), hz 9 (by decide)])
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 d3)) ?_ (by unfold coreCost; rw [fixed_length])
  have ha : (0 + 1 % p * bval (WilliamsPublishedForm.fixedWidthNatBits (natBitLength z.natAbs) z.natAbs)) % p =
      z.natAbs % p := by
    rw [bval_natWord, Nat.zero_add, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Nat.one_mul]
  apply WState.eq
  · funext i; by_cases hi : i = E
    · rw [hi, at2_sh_E, at2_sh_E, fixed_length, hlen]; ring
    · rw [at2_sh_ne _ _ _ _ _ hi, at2_sh_ne _ _ _ _ _ hi]
      show σB.sh i = σ.sh i
      rw [eB, eA]; simp [at2, Function.update_apply, hi]
  · show σB.st = σ.st
    exact sB.1
  · funext r
    by_cases hr : r = Pc
    · rw [hr, at2_val_Pc, at2_val_Pc, fixed_length, hlen]; ring
    · rw [at2_val_ne _ _ _ _ _ hr, at2_val_ne _ _ _ _ _ hr]
      simp only [regSt, coreSt]
      rw [ha, fixed_length]
      by_cases h4 : r = Rg 4
      · rw [if_pos h4, if_pos h4]
      · rw [if_neg h4, if_neg h4]
        by_cases h5 : r = Rg 5
        · rw [if_pos h5, if_pos h5]
        · rw [if_neg h5, if_neg h5]
          by_cases h6 : r = Rg 6
          · rw [if_pos h6, if_pos h6]
          · rw [if_neg h6, if_neg h6]
            by_cases h7 : r = Rg 7
            · rw [if_pos h7, if_pos h7]
            · rw [if_neg h7, if_neg h7]
              by_cases h3 : r = Rg 3
              · rw [if_pos h3, if_pos h3]
              · rw [if_neg h3, if_neg h3, eB]
                simp only [WState.setv_val, Function.update_apply, if_neg h5, if_neg h6, if_neg h7]
                rw [eA, at2_val_ne _ _ _ _ _ hr]
                by_cases h2 : r = Rg 2
                · rw [if_pos h2, h2]; simp
                · rw [if_neg h2]; simp [Function.update_apply, h2, h3]
  · show σB.cell = σ.cell
    exact sB.2.2.2

end NearCubicWires.WireExponent3_5.FinalPass.ThrRead
