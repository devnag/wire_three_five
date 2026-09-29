import Proof.Wire_3_5.FinalPass.ThrRead3

/-! # The THR residues from FRAMED payloads, part 4: the signed residue and the absolute residue

(P3:2585-2623, W17.) `modW2W neg` = `core2W` then `ThrCore.tailW neg`: `V = ((±z) mod p).toNat`
(`modW2_spec`). `absW2W` = `core2W` then `absTailW`: `V = |z| mod p` (`absW2_spec`). From `P = p` and the other
nine registers zero, both change only `V`, the head (past `intWord z`) and the position counter. Main declarations:
`fin_eq`, `absTailW`, **`modW2_spec`**, **`absW2_spec`**. Paper quantities: `w mod p` (the reduced coefficients) and
`|w| mod p` (the stack base's terms) for the selected children's numbers. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

variable {ns nr : ℕ} (cap : ℕ) (E : Fin (ns + 1)) (Pc : Fin nr) (Rg : Fin 10 ↪ Fin nr)

/-- The tails' common end: with `V := x` and `S, A, D, W, WD` cleared, only `V` differs from the entry. -/
theorem fin_eq (hPc : ∀ i, Rg i ≠ Pc) (σ : WState ns nr) (hz : ∀ i : Fin 10, i ≠ 0 → σ.val (Rg i) = 0)
    (p s a w x k : ℕ) :
    ((((((at2 (coreSt Rg σ p s a w) E Pc k).setv (Rg 1) x).setv (Rg 4) 0).setv (Rg 5) 0).setv (Rg 6) 0).setv
      (Rg 7) 0).setv (Rg 2) 0 = at2 (σ.setv (Rg 1) x) E Pc k := by
  have v : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => rne Rg h
  apply WState.eq
  · rfl
  · rfl
  · funext r
    by_cases hr : r = Pc
    · rw [hr]
      simp [at2, Function.update_apply, Ne.symm (hPc 1), Ne.symm (hPc 2), Ne.symm (hPc 4), Ne.symm (hPc 5),
        Ne.symm (hPc 6), Ne.symm (hPc 7)]
    · rw [at2_val_ne _ _ _ _ _ hr]
      simp only [WState.setv_val, Function.update_apply]
      by_cases h2 : r = Rg 2
      · rw [if_pos h2, h2, if_neg (v 2 1 (by decide)), hz 2 (by decide)]
      · rw [if_neg h2]
        by_cases h7 : r = Rg 7
        · rw [if_pos h7, h7, if_neg (v 7 1 (by decide)), hz 7 (by decide)]
        · rw [if_neg h7]
          by_cases h6 : r = Rg 6
          · rw [if_pos h6, h6, if_neg (v 6 1 (by decide)), hz 6 (by decide)]
          · rw [if_neg h6]
            by_cases h5 : r = Rg 5
            · rw [if_pos h5, h5, if_neg (v 5 1 (by decide)), hz 5 (by decide)]
            · rw [if_neg h5]
              by_cases h4 : r = Rg 4
              · rw [if_pos h4, h4, if_neg (v 4 1 (by decide)), hz 4 (by decide)]
              · rw [if_neg h4]
                by_cases h1 : r = Rg 1
                · rw [if_pos h1, if_pos h1]
                · rw [if_neg h1, if_neg h1, at2_val_ne _ _ _ _ _ hr]
                  simp only [coreSt, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h2]
                  by_cases h3 : r = Rg 3
                  · rw [if_pos h3, h3, hz 3 (by decide)]
                  · rw [if_neg h3]
  · rfl

/-- `coreCost` plus a tail. -/
def modCost2 (L p : ℕ) : ℕ := coreCost L p + 1 + (20 * p + 20)

/-- **The signed residue** of `intWord z` at the framed head: `V := ((±z) mod p).toNat`. -/
def modW2W (neg : Bool) : WM ns nr := .seq (core2W E Pc Rg) (tailW Rg neg)

theorem modW2_spec (hPc : ∀ i, Rg i ≠ Pc) (neg : Bool) (z : ℤ) (c rest : List Bool) (j p : ℕ) (hp : 1 ≤ p)
    (hpc : p ≤ cap) (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 2 * j + 1) (hpj : σ.val Pc = j)
    (hd : c.drop j = RepairRepresentation.intWord z ++ rest) (hP : σ.val (Rg 0) = p)
    (hz : ∀ i : Fin 10, i ≠ 0 → σ.val (Rg i) = 0) (hjc : j + (RepairRepresentation.intWord z).length ≤ cap) :
    WExec cap (modW2W E Pc Rg neg) σ
      (at2 (σ.setv (Rg 1) ((if neg then -z else z) % (p : ℤ)).toNat) E Pc
        (j + (RepairRepresentation.intWord z).length)) (modCost2 (natBitLength z.natAbs) p) := by
  have hpos : 0 < p := by omega
  have v : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => rne Rg h
  have d1 := core2_spec cap E Pc Rg hPc z c rest j p hp hpc σ hst hs hpj hd hP hz hjc
  have hv : ∀ i : Fin 10, (at2 (coreSt Rg σ p (decide (z < 0)).toNat (z.natAbs % p)
      (1 % p * 2 ^ natBitLength z.natAbs % p)) E Pc (j + (RepairRepresentation.intWord z).length)).val (Rg i) =
      (coreSt Rg σ p (decide (z < 0)).toNat (z.natAbs % p) (1 % p * 2 ^ natBitLength z.natAbs % p)).val (Rg i) :=
    fun i => at2_val_ne _ _ _ _ _ (hPc i)
  have d2 := tail_spec cap Rg neg p hpc _ (decide (z < 0)).toNat (z.natAbs % p)
    (1 % p * 2 ^ natBitLength z.natAbs % p) (Bool.toNat_le _)
    (by rw [hv]; simp [coreSt, v 2 4 (by decide), v 2 5 (by decide), v 2 6 (by decide), v 2 7 (by decide),
      v 2 3 (by decide)])
    (by rw [hv]; simp [coreSt])
    (by rw [hv]; simp [coreSt, v 5 4 (by decide)])
    (Nat.mod_lt _ hpos)
    (by rw [hv]; simp [coreSt, v 1 4 (by decide), v 1 5 (by decide), v 1 6 (by decide), v 1 7 (by decide),
      v 1 3 (by decide), v 1 2 (by decide), hz 1 (by decide)])
    (by rw [hv]; simp [coreSt, v 6 4 (by decide), v 6 5 (by decide)])
    (by rw [hv]; simp [coreSt, v 7 4 (by decide), v 7 5 (by decide), v 7 6 (by decide)])
    (Nat.mod_lt _ hpos)
  refine WExec.cast cap (WExec.seq d1 d2) ?_ le_rfl
  rw [fin_eq E Pc Rg hPc σ hz, res_eq z p hpos neg]

/-- `V := A`, then `D`, `W`, `WD`, `S` cleared. -/
def absTailW : WM ns nr :=
  .seq (WM.move (Rg 4) (Rg 1)) (.seq (WM.clear (Rg 5)) (.seq (WM.clear (Rg 6)) (.seq (WM.clear (Rg 7))
    (WM.clear (Rg 2)))))

theorem absTail_spec (p : ℕ) (hpc : p ≤ cap) (ρ : WState ns nr) (s a w : ℕ) (hs : s ≤ 1)
    (hS : ρ.val (Rg 2) = s) (hA : ρ.val (Rg 4) = a) (hD : ρ.val (Rg 5) = p - a) (ha : a < p)
    (hV : ρ.val (Rg 1) = 0) (hW : ρ.val (Rg 6) = w) (hWD : ρ.val (Rg 7) = p - w) (hw : w < p) :
    WExec cap (absTailW Rg) ρ
      ((((((ρ.setv (Rg 1) a).setv (Rg 4) 0).setv (Rg 5) 0).setv (Rg 6) 0).setv (Rg 7) 0).setv (Rg 2) 0)
      (20 * p + 20) := by
  have v : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => rne Rg h
  have m := wmove_spec cap (Rg 4) (Rg 1) (v 4 1 (by decide)) a ρ hA (by omega) (by omega)
  rw [hV, hA, Nat.zero_add] at m
  have c5 := wclear_spec cap (Rg 5) (p - a) ((ρ.setv (Rg 4) 0).setv (Rg 1) a)
    (by simp [Function.update_apply, v 5 1 (by decide), v 5 4 (by decide), hD])
    (by simp [Function.update_apply, v 5 1 (by decide), v 5 4 (by decide), hD]; omega)
  have c6 := wclear_spec cap (Rg 6) w (((ρ.setv (Rg 4) 0).setv (Rg 1) a).setv (Rg 5) 0)
    (by simp [Function.update_apply, v 6 1 (by decide), v 6 4 (by decide), v 6 5 (by decide), hW])
    (by simp [Function.update_apply, v 6 1 (by decide), v 6 4 (by decide), v 6 5 (by decide), hW]; omega)
  have c7 := wclear_spec cap (Rg 7) (p - w) ((((ρ.setv (Rg 4) 0).setv (Rg 1) a).setv (Rg 5) 0).setv (Rg 6) 0)
    (by simp [Function.update_apply, v 7 1 (by decide), v 7 4 (by decide), v 7 5 (by decide), v 7 6 (by decide),
      hWD])
    (by simp [Function.update_apply, v 7 1 (by decide), v 7 4 (by decide), v 7 5 (by decide), v 7 6 (by decide),
      hWD]; omega)
  have c2 := wclear_spec cap (Rg 2) s
    (((((ρ.setv (Rg 4) 0).setv (Rg 1) a).setv (Rg 5) 0).setv (Rg 6) 0).setv (Rg 7) 0)
    (by simp [Function.update_apply, v 2 1 (by decide), v 2 4 (by decide), v 2 5 (by decide), v 2 6 (by decide),
      v 2 7 (by decide), hS])
    (by simp [Function.update_apply, v 2 1 (by decide), v 2 4 (by decide), v 2 5 (by decide), v 2 6 (by decide),
      v 2 7 (by decide), hS]; omega)
  refine WExec.cast cap (WExec.seq m (WExec.seq c5 (WExec.seq c6 (WExec.seq c7 c2)))) ?_ (by omega)
  rw [wsetv_comm ρ (0 : ℕ) a (v 4 1 (by decide))]

/-- **The absolute residue** of `intWord z` at the framed head: `V := |z| mod p`. -/
def absW2W : WM ns nr := .seq (core2W E Pc Rg) (absTailW Rg)

theorem absW2_spec (hPc : ∀ i, Rg i ≠ Pc) (z : ℤ) (c rest : List Bool) (j p : ℕ) (hp : 1 ≤ p)
    (hpc : p ≤ cap) (σ : WState ns nr) (hst : σ.st E = frame c) (hs : σ.sh E = 2 * j + 1) (hpj : σ.val Pc = j)
    (hd : c.drop j = RepairRepresentation.intWord z ++ rest) (hP : σ.val (Rg 0) = p)
    (hz : ∀ i : Fin 10, i ≠ 0 → σ.val (Rg i) = 0) (hjc : j + (RepairRepresentation.intWord z).length ≤ cap) :
    WExec cap (absW2W E Pc Rg) σ (at2 (σ.setv (Rg 1) (z.natAbs % p)) E Pc
      (j + (RepairRepresentation.intWord z).length)) (modCost2 (natBitLength z.natAbs) p) := by
  have hpos : 0 < p := by omega
  have v : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => rne Rg h
  have d1 := core2_spec cap E Pc Rg hPc z c rest j p hp hpc σ hst hs hpj hd hP hz hjc
  have hv : ∀ i : Fin 10, (at2 (coreSt Rg σ p (decide (z < 0)).toNat (z.natAbs % p)
      (1 % p * 2 ^ natBitLength z.natAbs % p)) E Pc (j + (RepairRepresentation.intWord z).length)).val (Rg i) =
      (coreSt Rg σ p (decide (z < 0)).toNat (z.natAbs % p) (1 % p * 2 ^ natBitLength z.natAbs % p)).val (Rg i) :=
    fun i => at2_val_ne _ _ _ _ _ (hPc i)
  have d2 := absTail_spec cap Rg p hpc _ (decide (z < 0)).toNat (z.natAbs % p)
    (1 % p * 2 ^ natBitLength z.natAbs % p) (Bool.toNat_le _)
    (by rw [hv]; simp [coreSt, v 2 4 (by decide), v 2 5 (by decide), v 2 6 (by decide), v 2 7 (by decide),
      v 2 3 (by decide)])
    (by rw [hv]; simp [coreSt])
    (by rw [hv]; simp [coreSt, v 5 4 (by decide)])
    (Nat.mod_lt _ hpos)
    (by rw [hv]; simp [coreSt, v 1 4 (by decide), v 1 5 (by decide), v 1 6 (by decide), v 1 7 (by decide),
      v 1 3 (by decide), v 1 2 (by decide), hz 1 (by decide)])
    (by rw [hv]; simp [coreSt, v 6 4 (by decide), v 6 5 (by decide)])
    (by rw [hv]; simp [coreSt, v 7 4 (by decide), v 7 5 (by decide), v 7 6 (by decide)])
    (Nat.mod_lt _ hpos)
  refine WExec.cast cap (WExec.seq d1 d2) ?_ (by unfold modCost2; omega)
  rw [fin_eq E Pc Rg hPc σ hz]

end NearCubicWires.WireExponent3_5.FinalPass.ThrRead
