import Proof.Wire_3_5.FinalPass.ThrRead1

/-! # The THR residues from FRAMED payloads, part 2: one signed integer's sign, length and digits

(P3:2585-2623, W17.) `intWord z = [z < 0] ++ 1^L 0 ++ bits` read at stride two (`at2`): `head2W` takes
the sign into `S` and the length `L` into `Ln`; `bitLoop2W` folds the digits (least significant first) into
`A = |z| mod p` with `W = 2^k mod p`, all registers below `p`. `core2W` = head, `ThrCore.initW`, digits: it leaves
`A = |z| mod p`, `D = p − A`, the sign in `S`, and the head past the word. Main declarations: `head2_spec`,
`bitLoop2_spec`, **`core2_spec`**. Paper quantity: `|w_i| mod p` for a coefficient `w_i` of `L_g`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

variable {ns nr : ℕ} (cap : ℕ) (E : Fin (ns + 1)) (Pc : Fin nr) (Rg : Fin 10 ↪ Fin nr)

/-- Sign into `S = Rg 2`, length into `Ln = Rg 3`, the head at the first digit. -/
def head2W : WM ns nr :=
  .seq (.ifs E (.inc (Rg 2)) .skip) (.seq (adv2W E Pc) (.seq (cnt2W E Pc (Rg 3)) (adv2W E Pc)))

theorem intWord_drop1 (z : ℤ) (rest : List Bool) : RepairRepresentation.intWord z ++ rest =
    decide (z < 0) :: (List.replicate (natBitLength z.natAbs) true ++ false ::
      (WilliamsPublishedForm.fixedWidthNatBits (natBitLength z.natAbs) z.natAbs ++ rest)) := by
  simp [RepairRepresentation.intWord, natWord_split]

theorem head2_spec (hPc : ∀ i, Rg i ≠ Pc) (z : ℤ) (c rest : List Bool) (j : ℕ) (σ : WState ns nr)
    (hst : σ.st E = frame c) (hs : σ.sh E = 2 * j + 1) (hp : σ.val Pc = j)
    (hd : c.drop j = RepairRepresentation.intWord z ++ rest) (hS : σ.val (Rg 2) = 0) (hLn : σ.val (Rg 3) = 0)
    (hjc : j + 2 + natBitLength z.natAbs ≤ cap) :
    WExec cap (head2W E Pc Rg) σ
      (at2 ((σ.setv (Rg 2) (decide (z < 0)).toNat).setv (Rg 3) (natBitLength z.natAbs)) E Pc
        (j + 2 + natBitLength z.natAbs)) (13 * natBitLength z.natAbs + 22) := by
  have hd1 := hd
  rw [intWord_drop1] at hd1
  have hb : wbit σ E = decide (z < 0) := by unfold wbit; rw [hst, hs]; exact frame_read c j _ _ hd1
  obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv (Rg 2) (decide (z < 0)).toNat := ⟨_, rfl⟩
  have d1 : WExec cap (.ifs E (.inc (Rg 2)) .skip) σ σ1 4 := by
    rw [e1]
    cases h : decide (z < 0)
    · have e : σ.setv (Rg 2) (false).toNat = σ := by
        rw [show (false).toNat = 0 from rfl, ← hS, wsetv_same]
      rw [e]
      exact WExec.mono (WExec.ifsF (by rw [hb, h]) (WExec.skip σ)) (by omega)
    · have hi := WExec.inc (cap := cap) (Rg 2) σ (by omega)
      rw [hS] at hi
      exact WExec.mono (WExec.ifsT (by rw [hb, h]) hi) (by omega)
  have s1 : σ1.st = σ.st ∧ σ1.sh = σ.sh ∧ σ1.val Pc = j ∧ σ1.val (Rg 3) = 0 := by
    rw [e1]; refine ⟨rfl, rfl, ?_, ?_⟩
    · simp [Function.update_apply, Ne.symm (hPc 2), hp]
    · simp [Function.update_apply, rne Rg (show (3 : Fin 10) ≠ 2 by decide), hLn]
  have d2 := adv2_spec cap E Pc σ1 j (by rw [s1.2.1, hs]) s1.2.2.1 (by omega)
  have d3 := cnt2_spec cap E Pc (Rg 3) (Ne.symm (hPc 3)) c
    (WilliamsPublishedForm.fixedWidthNatBits (natBitLength z.natAbs) z.natAbs ++ rest) (natBitLength z.natAbs)
    (at2 σ1 E Pc (j + 1)) (j + 1) 0 (by simp [s1.1, hst]) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _)
    (frame_next c j _ _ hd1) (by rw [at2_val_ne _ _ _ _ _ (hPc 3), s1.2.2.2]) (by omega) (by omega)
  have d4 := adv2_spec cap E Pc (at2 ((at2 σ1 E Pc (j + 1)).setv (Rg 3) (0 + natBitLength z.natAbs)) E Pc
    (j + 1 + natBitLength z.natAbs)) (j + 1 + natBitLength z.natAbs) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _)
    (by omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ?_ (by omega)
  rw [e1]
  apply WState.eq
  · funext i; by_cases hi : i = E
    · rw [hi, at2_sh_E, at2_sh_E]; ring
    · simp [at2, Function.update_apply, hi]
  · rfl
  · funext r; by_cases hr : r = Pc
    · rw [hr, at2_val_Pc, at2_val_Pc]; ring
    · by_cases h3 : r = Rg 3
      · subst h3; simp [at2, Function.update_apply, hr]
      · simp [at2, Function.update_apply, hr, h3]
  · rfl

/-- One framed digit: `A += W` if the digit is `1`, `W := 2W`, all modulo `p`. -/
def bit2W : WM ns nr :=
  .seq (.dec (Rg 3)) (.seq (.ifs E (addModW (Rg 4) (Rg 5) (Rg 6) (Rg 8) (Rg 9)) .skip)
    (.seq (addModW (Rg 6) (Rg 7) (Rg 6) (Rg 8) (Rg 9)) (adv2W E Pc)))

/-- `Ln` framed digits. -/
def bitLoop2W : WM ns nr := .whr (Rg 3) (bit2W E Pc Rg)

/-- One framed digit's step bound. -/
def bitCost2 (p : ℕ) : ℕ := bitCost p + 6

/-- The registers after the digits `bs` (from `A = a`, `W = w`); heads unchanged. -/
def regSt (p : ℕ) (σ : WState ns nr) (a w : ℕ) (bs : List Bool) : WState ns nr :=
  ⟨σ.sh, σ.st,
    fun r => if r = Rg 4 then (a + w * bval bs) % p else if r = Rg 5 then p - (a + w * bval bs) % p
      else if r = Rg 6 then (w * 2 ^ bs.length) % p else if r = Rg 7 then p - (w * 2 ^ bs.length) % p
      else if r = Rg 3 then 0 else σ.val r, σ.cell⟩

theorem bitLoop2_spec (hPc : ∀ i, Rg i ≠ Pc) (p : ℕ) (hp : 1 ≤ p) (hpc : p ≤ cap) (c rest : List Bool) :
    ∀ (bs : List Bool) (σ : WState ns nr) (a w j : ℕ), σ.st E = frame c → σ.sh E = 2 * j + 1 → σ.val Pc = j →
      c.drop j = bs ++ rest → j + bs.length ≤ cap →
      σ.val (Rg 3) = bs.length → bs.length ≤ cap → σ.val (Rg 4) = a → σ.val (Rg 5) = p - a → a < p →
      σ.val (Rg 6) = w → σ.val (Rg 7) = p - w → w < p → σ.val (Rg 8) = 0 → σ.val (Rg 9) = 0 →
      WExec cap (bitLoop2W E Pc Rg) σ (at2 (regSt Rg p σ a w bs) E Pc (j + bs.length))
        (bs.length * (bitCost2 p + 2) + 1)
  | [], σ, a, w, j, _, hs, hp', _, _, hL, _, hA, hD, ha, hW, hWD, hw, _, _ => by
    refine WExec.cast cap (WExec.whrF (by rw [hL]; rfl)) ?_ (by simp)
    apply WState.eq
    · funext i; by_cases hi : i = E
      · subst hi; simp [at2, regSt, hs]
      · simp [at2, regSt, Function.update_apply, hi]
    · rfl
    · funext r
      by_cases hP : r = Pc
      · rw [hP, at2_val_Pc, hp']; simp
      · rw [at2_val_ne _ _ _ _ _ hP]; unfold regSt; dsimp only
        by_cases h4 : r = Rg 4
        · subst h4; simp [hA, bval, Nat.mod_eq_of_lt ha]
        · by_cases h5 : r = Rg 5
          · subst h5; simp [h4, hD, bval, Nat.mod_eq_of_lt ha]
          · by_cases h6 : r = Rg 6
            · subst h6; simp [h4, h5, hW, Nat.mod_eq_of_lt hw]
            · by_cases h7 : r = Rg 7
              · subst h7; simp [h4, h5, h6, hWD, Nat.mod_eq_of_lt hw]
              · by_cases h3 : r = Rg 3
                · subst h3; simp [h4, h5, h6, h7, hL]
                · simp [h4, h5, h6, h7, h3]
    · rfl
  | b :: bs, σ, a, w, j, hst, hs, hp', hd, hjc, hL, hLc, hA, hD, ha, hW, hWD, hw, hT, hU => by
    have hpos : 0 < p := by omega
    have d1 := WExec.dec (cap := cap) (Rg 3) σ (by rw [hL]; exact hLc)
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv (Rg 3) (σ.val (Rg 3) - 1) := ⟨_, rfl⟩
    rw [← e1] at d1
    have g1 : ∀ i : Fin 10, i ≠ 3 → σ1.val (Rg i) = σ.val (Rg i) := fun i hi => by
      rw [e1]; simp [Function.update_apply, rne Rg hi]
    have hb : wbit σ1 E = b := by
      unfold wbit; rw [e1]; simp only [WState.setv_st, WState.setv_sh]; rw [hst, hs]
      exact frame_read c j b _ (by rw [hd]; rfl)
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = if b then (((σ1.setv (Rg 4) ((a + w) % p)).setv (Rg 5) (p - (a + w) % p)).setv (Rg 8) 0)
        else σ1 := ⟨_, rfl⟩
    have d2 : WExec cap (.ifs E (addModW (Rg 4) (Rg 5) (Rg 6) (Rg 8) (Rg 9)) .skip) σ1 σ2
        (18 * p + 5 + p * (7 * p + 12) + 1) := by
      cases b
      · rw [e2]; exact WExec.mono (WExec.ifsF (by rw [hb]) (WExec.skip _)) (by omega)
      · rw [e2]
        have := addMod_spec cap (Rg 4) (Rg 5) (Rg 6) (Rg 8) (Rg 9) (rne Rg (by decide)) (rne Rg (by decide))
          (rne Rg (by decide)) (rne Rg (by decide)) (rne Rg (by decide)) (rne Rg (by decide)) p hpc σ1 a w
          (by rw [g1 8 (by decide), hT]) (by rw [g1 9 (by decide), hU]) (by rw [g1 6 (by decide), hW])
          (by omega) (by rw [g1 4 (by decide), hA]) (by rw [g1 5 (by decide), hD]) ha
        refine WExec.ifsT (by rw [hb]) (WExec.mono this ?_)
        have : w * (7 * p + 12) ≤ p * (7 * p + 12) := Nat.mul_le_mul_right _ hw.le
        omega
    have a2 : σ2.val (Rg 4) = (a + b.toNat * w) % p := by
      rw [e2]; cases b
      · simp [g1 4 (by decide), hA, Nat.mod_eq_of_lt ha]
      · simp [Function.update_apply, rne Rg (show (4 : Fin 10) ≠ 8 by decide),
          rne Rg (show (4 : Fin 10) ≠ 5 by decide)]
    have g2 : ∀ i : Fin 10, i ≠ 4 → i ≠ 5 → σ2.val (Rg i) = σ1.val (Rg i) := fun i h4 h5 => by
      rw [e2]; cases b
      · rfl
      · by_cases h8 : i = 8
        · subst h8; simp [Function.update_apply, g1 8 (by decide), hT]
        · simp [Function.update_apply, rne Rg h4, rne Rg h5, rne Rg h8]
    have a2D : σ2.val (Rg 5) = p - (a + b.toNat * w) % p := by
      rw [e2]; cases b
      · simp [g1 5 (by decide), hD, Nat.mod_eq_of_lt ha]
      · simp [Function.update_apply, rne Rg (show (5 : Fin 10) ≠ 8 by decide)]
    have s2 : σ2.st = σ.st ∧ σ2.sh = σ.sh ∧ σ2.cell = σ.cell := by rw [e2, e1]; cases b <;> simp
    have p2 : σ2.val Pc = j := by
      rw [e2, e1]; cases b <;> simp [Function.update_apply, Ne.symm (hPc 3), Ne.symm (hPc 4), Ne.symm (hPc 5),
        Ne.symm (hPc 8), hp']
    have d3 := addMod_spec cap (Rg 6) (Rg 7) (Rg 6) (Rg 8) (Rg 9) (rne Rg (by decide)) (rne Rg (by decide))
      (rne Rg (by decide)) (rne Rg (by decide)) (rne Rg (by decide)) (rne Rg (by decide)) p hpc σ2 w w
      (by rw [g2 8 (by decide) (by decide), g1 8 (by decide), hT])
      (by rw [g2 9 (by decide) (by decide), g1 9 (by decide), hU])
      (by rw [g2 6 (by decide) (by decide), g1 6 (by decide), hW]) (by omega)
      (by rw [g2 6 (by decide) (by decide), g1 6 (by decide), hW])
      (by rw [g2 7 (by decide) (by decide), g1 7 (by decide), hWD]) hw
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = ((σ2.setv (Rg 6) ((w + w) % p)).setv (Rg 7) (p - (w + w) % p)).setv (Rg 8) 0 :=
      ⟨_, rfl⟩
    rw [← e3] at d3
    have s3 : σ3.sh E = 2 * j + 1 ∧ σ3.val Pc = j := by
      rw [e3]; refine ⟨by simp [s2.2.1, hs], ?_⟩
      simp [Function.update_apply, Ne.symm (hPc 6), Ne.symm (hPc 7), Ne.symm (hPc 8), p2]
    have hjc' : j < cap := by simp at hjc; omega
    have d4 := adv2_spec cap E Pc σ3 j s3.1 s3.2 hjc'
    have body : WExec cap (bit2W E Pc Rg) σ (at2 σ3 E Pc (j + 1)) (bitCost2 p) := by
      refine WExec.mono (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ?_
      have : w * (7 * p + 12) ≤ p * (7 * p + 12) := Nat.mul_le_mul_right _ hw.le
      unfold bitCost2 bitCost; omega
    have v4 : ∀ i : Fin 10, (at2 σ3 E Pc (j + 1)).val (Rg i) = σ3.val (Rg i) := fun i =>
      at2_val_ne _ _ _ _ _ (hPc i)
    have f3 : ∀ i : Fin 10, i ≠ 6 → i ≠ 7 → i ≠ 8 → σ3.val (Rg i) = σ2.val (Rg i) := fun i h6 h7 h8 => by
      rw [e3]; simp [Function.update_apply, rne Rg h6, rne Rg h7, rne Rg h8]
    have h3st : σ3.st = σ.st := by rw [e3]; simp [s2.1]
    have ih := bitLoop2_spec hPc p hp hpc c rest bs (at2 σ3 E Pc (j + 1)) ((a + b.toNat * w) % p) ((w + w) % p)
      (j + 1) (by simp [h3st, hst]) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _) (frame_next c j b _ (by rw [hd]; rfl))
      (by simp at hjc; omega)
      (by rw [v4, f3 3 (by decide) (by decide) (by decide), g2 3 (by decide) (by decide), e1]; simp [hL])
      (by simp at hLc; omega) (by rw [v4, f3 4 (by decide) (by decide) (by decide), a2])
      (by rw [v4, f3 5 (by decide) (by decide) (by decide), a2D]) (Nat.mod_lt _ hpos)
      (by rw [v4, e3]; simp [Function.update_apply, rne Rg (show (6 : Fin 10) ≠ 8 by decide),
        rne Rg (show (6 : Fin 10) ≠ 7 by decide)])
      (by rw [v4, e3]; simp [Function.update_apply, rne Rg (show (7 : Fin 10) ≠ 8 by decide)]) (Nat.mod_lt _ hpos)
      (by rw [v4, e3]; simp)
      (by rw [v4, f3 9 (by decide) (by decide) (by decide), g2 9 (by decide) (by decide), g1 9 (by decide), hU])
    refine WExec.cast cap (WExec.whrT (by rw [hL]; simp) body ih) ?_
      (by rw [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
    have hA' : ((a + b.toNat * w) % p + (w + w) % p * bval bs) % p = (a + w * bval (b :: bs)) % p := by
      rw [mod_step]; rfl
    have hW' : (w + w) % p * 2 ^ bs.length % p = w * 2 ^ (b :: bs).length % p := by rw [pow_step]; rfl
    have h3c : σ3.cell = σ.cell := by rw [e3]; simp [s2.2.2]
    apply WState.eq
    · funext i; by_cases hi : i = E
      · rw [hi, at2_sh_E, at2_sh_E, List.length_cons]; ring
      · rw [at2_sh_ne _ _ _ _ _ hi, at2_sh_ne _ _ _ _ _ hi]
        show (at2 σ3 E Pc (j + 1)).sh i = σ.sh i
        rw [at2_sh_ne _ _ _ _ _ hi, e3]; simp [s2.2.1]
    · show σ3.st = σ.st
      exact h3st
    · funext r
      by_cases hP : r = Pc
      · rw [hP, at2_val_Pc, at2_val_Pc, List.length_cons]; ring
      · rw [at2_val_ne _ _ _ _ _ hP, at2_val_ne _ _ _ _ _ hP]; unfold regSt; dsimp only
        by_cases h4 : r = Rg 4
        · subst h4; simp only [if_pos rfl, ite_true]; exact hA'
        · rw [if_neg h4, if_neg h4]
          by_cases h5 : r = Rg 5
          · subst h5; simp only [if_pos rfl, ite_true]; rw [hA']
          · rw [if_neg h5, if_neg h5]
            by_cases h6 : r = Rg 6
            · subst h6; simp only [if_pos rfl, ite_true]; exact hW'
            · rw [if_neg h6, if_neg h6]
              by_cases h7 : r = Rg 7
              · subst h7; simp only [if_pos rfl, ite_true]; rw [hW']
              · rw [if_neg h7, if_neg h7]
                by_cases h3 : r = Rg 3
                · subst h3; simp only [if_pos rfl, ite_true]
                · rw [if_neg h3, if_neg h3, at2_val_ne _ _ _ _ _ hP, e3]
                  simp only [WState.setv_val, Function.update_apply, if_neg h6, if_neg h7]
                  by_cases h8 : r = Rg 8
                  · subst h8; simp [hT]
                  · rw [if_neg h8, e2, e1]
                    cases b <;> simp [Function.update_apply, h4, h5, h8, h3]
    · show σ3.cell = σ.cell
      exact h3c

end NearCubicWires.WireExponent3_5.FinalPass.ThrRead
