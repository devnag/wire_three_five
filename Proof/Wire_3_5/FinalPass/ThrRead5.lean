import Proof.Wire_3_5.FinalPass.ThrRead4

/-! # FRAMED payloads, part 5: advancing, rewinding, skipping an integer, reading a natural number exactly

(P3:2543-2551, 2585-2623, W17.) Navigation in a framed payload (`at2`): `advLoopW` (`k` steps, `k`
counted down), `rew2W` (back to cell `0`, the position counter cleared), `skip2W` (past one `intWord`), and
`natW2W` (`V := v` exactly from `natWord v`, least significant digit first, no modulus: the payload's support size
and child count). Main declarations: `setv_eq_self`, `advLoop_spec`, `rew2_spec`, `skip2_spec`, `addTo_spec`,
`bitNLoop_spec`, **`natW2_spec`**. Paper quantities: `|supp_i|` and `|children_i|` of circuit `i`'s retained top. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.ThrRead
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.ThrCore

theorem setv_eq_self {ns nr : ℕ} (σ : WState ns nr) (r : Fin nr) (v : ℕ) (h : σ.val r = v) : σ.setv r v = σ := by
  subst h; exact wsetv_same σ r

variable {ns nr : ℕ} (cap : ℕ) (E : Fin (ns + 1)) (Pc : Fin nr) (Rg : Fin 10 ↪ Fin nr)

/-! ## Advancing and rewinding -/

/-- `k` framed steps, `k` counted down in `C`. -/
def advLoopW (C : Fin nr) : WM ns nr := .whr C (.seq (.dec C) (adv2W E Pc))

theorem advLoop_spec (C : Fin nr) (hC : C ≠ Pc) : ∀ (k : ℕ) (σ : WState ns nr) (j : ℕ), σ.val C = k → k ≤ cap →
    σ.sh E = 2 * j + 1 → σ.val Pc = j → j + k ≤ cap →
    WExec cap (advLoopW E Pc C) σ (at2 (σ.setv C 0) E Pc (j + k)) (11 * k + 1)
  | 0, σ, j, hk, _, hs, hp, _ => by
    refine WExec.cast cap (WExec.whrF hk) ?_ (by omega)
    rw [setv_eq_self σ C 0 hk, Nat.add_zero, at2_self σ E Pc j hs hp]
  | k + 1, σ, j, hk, hkc, hs, hp, hjk => by
    have d1 := WExec.dec (cap := cap) C σ (by omega)
    have d2 := adv2_spec cap E Pc (σ.setv C (σ.val C - 1)) j (by simpa using hs)
      (by simp [Function.update_apply, Ne.symm hC, hp]) (by omega)
    have ih := advLoop_spec C hC k (at2 (σ.setv C (σ.val C - 1)) E Pc (j + 1)) (j + 1)
      (by rw [at2_val_ne _ _ _ _ _ hC]; simp [hk]) (by omega) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _) (by omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 d2) ih) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = E
      · rw [hi, at2_sh_E, at2_sh_E]; ring
      · simp [at2, Function.update_apply, hi]
    · rfl
    · funext r; by_cases hr : r = Pc
      · rw [hr, at2_val_Pc, at2_val_Pc]; ring
      · by_cases h2 : r = C
        · rw [h2]; simp [at2, Function.update_apply, hC]
        · simp [at2, Function.update_apply, hr, h2]
    · rfl

/-- Back to the content start (two cells per counted step). -/
def rewLoopW : WM ns nr := .whr Pc (.seq (.dec Pc) (.seq (.bwd E) (.bwd E)))

/-- Back to cell `0`, the position counter cleared. -/
def rew2W : WM ns nr := .seq (rewLoopW E Pc) (.bwd E)

theorem rewLoop_spec : ∀ (j : ℕ) (σ : WState ns nr), σ.val Pc = j → j ≤ cap → σ.sh E = 2 * j + 1 →
    WExec cap (rewLoopW E Pc) σ ((σ.setv Pc 0).seth E 1) (7 * j + 1)
  | 0, σ, hp, _, hs => by
    refine WExec.cast cap (WExec.whrF hp) ?_ (by omega)
    apply WState.eq
    · funext i; by_cases hi : i = E
      · rw [hi]; simp [hs]
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases hr : r = Pc
      · rw [hr]; simp [hp]
      · simp [Function.update_apply, hr]
    · rfl
  | j + 1, σ, hp, hc, hs => by
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv Pc (σ.val Pc - 1) := ⟨_, rfl⟩
    have d1 := WExec.dec (cap := cap) Pc σ (by omega)
    rw [← e1] at d1
    have d2 := WExec.bwd (cap := cap) E σ1
    have d3 := WExec.bwd (cap := cap) E (σ1.seth E (σ1.sh E - 1))
    have ih := rewLoop_spec j ((σ1.seth E (σ1.sh E - 1)).seth E ((σ1.seth E (σ1.sh E - 1)).sh E - 1))
      (by rw [e1]; simp [hp]) (by omega) (by rw [e1]; simp [hs]; omega)
    refine WExec.cast cap (WExec.whrT (by omega) (WExec.seq d1 (WExec.seq d2 d3)) ih) ?_ (by omega)
    rw [e1]
    apply WState.eq
    · funext i; by_cases hi : i = E
      · rw [hi]; simp
      · simp [Function.update_apply, hi]
    · rfl
    · funext r; by_cases hr : r = Pc
      · rw [hr]; simp
      · simp [Function.update_apply, hr]
    · rfl

theorem rew2_spec (j : ℕ) (σ : WState ns nr) (hp : σ.val Pc = j) (hc : j ≤ cap) (hs : σ.sh E = 2 * j + 1) :
    WExec cap (rew2W E Pc) σ ((σ.setv Pc 0).seth E 0) (7 * j + 3) := by
  have d1 := rewLoop_spec cap E Pc j σ hp hc hs
  have d2 := WExec.bwd (cap := cap) E ((σ.setv Pc 0).seth E 1)
  refine WExec.cast cap (WExec.seq d1 d2) ?_ (by omega)
  apply WState.eq
  · funext i; by_cases hi : i = E
    · rw [hi]; simp
    · simp [Function.update_apply, hi]
  · rfl
  · rfl
  · rfl

/-! ## Skipping one integer -/

/-- Past `intWord z`: the sign, the length (counted into `Ln`), the separator, then `Ln` digits. -/
def skip2W : WM ns nr :=
  .seq (adv2W E Pc) (.seq (cnt2W E Pc (Rg 3)) (.seq (adv2W E Pc) (advLoopW E Pc (Rg 3))))

theorem skip2_spec (hPc : ∀ i, Rg i ≠ Pc) (z : ℤ) (c rest : List Bool) (j : ℕ) (σ : WState ns nr)
    (hst : σ.st E = frame c) (hs : σ.sh E = 2 * j + 1) (hp : σ.val Pc = j)
    (hd : c.drop j = RepairRepresentation.intWord z ++ rest) (hLn : σ.val (Rg 3) = 0)
    (hjc : j + (RepairRepresentation.intWord z).length ≤ cap) :
    WExec cap (skip2W E Pc Rg) σ (at2 σ E Pc (j + (RepairRepresentation.intWord z).length))
      (24 * natBitLength z.natAbs + 19) := by
  have hlen := intWord_length' z
  have hd1 := hd
  rw [intWord_drop1] at hd1
  have d1 := adv2_spec cap E Pc σ j hs hp (by omega)
  have d2 := cnt2_spec cap E Pc (Rg 3) (Ne.symm (hPc 3)) c
    (WilliamsPublishedForm.fixedWidthNatBits (natBitLength z.natAbs) z.natAbs ++ rest) (natBitLength z.natAbs)
    (at2 σ E Pc (j + 1)) (j + 1) 0 (by simp [hst]) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _)
    (frame_next c j _ _ hd1) (by rw [at2_val_ne _ _ _ _ _ (hPc 3), hLn]) (by omega) (by omega)
  obtain ⟨σ2, e2⟩ : ∃ τ, τ = at2 ((at2 σ E Pc (j + 1)).setv (Rg 3) (0 + natBitLength z.natAbs)) E Pc
      (j + 1 + natBitLength z.natAbs) := ⟨_, rfl⟩
  rw [← e2] at d2
  have d3 := adv2_spec cap E Pc σ2 (j + 1 + natBitLength z.natAbs) (by rw [e2, at2_sh_E])
    (by rw [e2, at2_val_Pc]) (by omega)
  have d4 := advLoop_spec cap E Pc (Rg 3) (hPc 3) (natBitLength z.natAbs)
    (at2 σ2 E Pc (j + 1 + natBitLength z.natAbs + 1)) (j + 1 + natBitLength z.natAbs + 1)
    (by rw [at2_val_ne _ _ _ _ _ (hPc 3), e2, at2_val_ne _ _ _ _ _ (hPc 3)]; simp) (by omega) (at2_sh_E _ _ _ _)
    (at2_val_Pc _ _ _ _) (by omega)
  refine WExec.cast cap (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) ?_ (by omega)
  rw [e2]
  apply WState.eq
  · funext i; by_cases hi : i = E
    · rw [hi, at2_sh_E, at2_sh_E, hlen]; ring
    · simp [at2, Function.update_apply, hi]
  · rfl
  · funext r; by_cases hr : r = Pc
    · rw [hr, at2_val_Pc, at2_val_Pc, hlen]; ring
    · by_cases h3 : r = Rg 3
      · rw [h3]; simp [at2, Function.update_apply, hPc 3, hLn]
      · simp [at2, Function.update_apply, hr, h3]
  · rfl

/-! ## One natural number, exactly -/

/-- `X := X + Src` (through `T = Rg 8`, `U = Rg 9`). -/
def addToW (X Src : Fin nr) : WM ns nr := .seq (Hash4.wcopyR Src (Rg 8) (Rg 9)) (WM.move (Rg 8) X)

theorem addTo_spec (X Src : Fin nr) (hXT : X ≠ Rg 8) (hST : Src ≠ Rg 8) (hSU : Src ≠ Rg 9) (σ : WState ns nr)
    (hT : σ.val (Rg 8) = 0) (hU : σ.val (Rg 9) = 0) (hS : σ.val Src ≤ cap) (hX : σ.val X + σ.val Src ≤ cap) :
    WExec cap (addToW Rg X Src) σ (σ.setv X (σ.val X + σ.val Src)) (25 * σ.val Src + 5) := by
  have d1 := Hash4.wcopyR_spec cap Src (Rg 8) (Rg 9) hST hSU (rne Rg (by decide)) σ hT hU hS
  have d2 := wmove_spec cap (Rg 8) X (Ne.symm hXT) (σ.val Src) (σ.setv (Rg 8) (σ.val Src)) (by simp) (by simp; omega)
    (by simp [Function.update_apply, hXT]; omega)
  refine WExec.cast cap (WExec.seq d1 d2) ?_ (by omega)
  refine WState.eq rfl rfl ?_ rfl
  funext r; by_cases h1 : r = X
  · rw [h1]; simp [Function.update_apply, hXT]
  · by_cases h2 : r = Rg 8
    · rw [h2]; simp [Function.update_apply, Ne.symm hXT, hT]
    · simp [Function.update_apply, h1, h2]

/-- One exact digit: `A += W` if the digit is `1`, `W := 2W`. -/
def bitNW : WM ns nr :=
  .seq (.dec (Rg 3)) (.seq (.ifs E (addToW Rg (Rg 4) (Rg 6)) .skip) (.seq (addToW Rg (Rg 6) (Rg 6)) (adv2W E Pc)))

/-- `Ln` exact digits. -/
def bitNLoopW : WM ns nr := .whr (Rg 3) (bitNW E Pc Rg)

/-- The registers after the exact digits `bs` (from `A = a`, `W = w`); heads unchanged. -/
def nSt (σ : WState ns nr) (a w : ℕ) (bs : List Bool) : WState ns nr :=
  ⟨σ.sh, σ.st, fun r => if r = Rg 4 then a + w * bval bs else if r = Rg 6 then w * 2 ^ bs.length
    else if r = Rg 3 then 0 else σ.val r, σ.cell⟩

theorem bitNLoop_spec (hPc : ∀ i, Rg i ≠ Pc) (c rest : List Bool) (M : ℕ) (hM : M ≤ cap) :
    ∀ (bs : List Bool) (σ : WState ns nr) (a w j : ℕ), σ.st E = frame c → σ.sh E = 2 * j + 1 → σ.val Pc = j →
      c.drop j = bs ++ rest → j + bs.length ≤ cap → σ.val (Rg 3) = bs.length → bs.length ≤ cap →
      σ.val (Rg 4) = a → σ.val (Rg 6) = w → a + w * bval bs ≤ cap → w * 2 ^ bs.length ≤ M →
      σ.val (Rg 8) = 0 → σ.val (Rg 9) = 0 →
      WExec cap (bitNLoopW E Pc Rg) σ (at2 (nSt Rg σ a w bs) E Pc (j + bs.length)) (bs.length * (50 * M + 24) + 1)
  | [], σ, a, w, j, _, hs, hp, _, _, hL, _, hA, hW, _, _, _, _ => by
    refine WExec.cast cap (WExec.whrF (by rw [hL]; rfl)) ?_ (by simp)
    apply WState.eq
    · funext i; by_cases hi : i = E
      · rw [hi, at2_sh_E, hs]; rfl
      · rw [at2_sh_ne _ _ _ _ _ hi]; rfl
    · rfl
    · funext r
      by_cases hP : r = Pc
      · rw [hP, at2_val_Pc, hp]; simp
      · rw [at2_val_ne _ _ _ _ _ hP]; unfold nSt; dsimp only
        by_cases h4 : r = Rg 4
        · rw [h4]; simp [hA, bval]
        · by_cases h6 : r = Rg 6
          · rw [h6]; simp [rne Rg (show (6 : Fin 10) ≠ 4 by decide), hW]
          · by_cases h3 : r = Rg 3
            · rw [h3]; simp [rne Rg (show (3 : Fin 10) ≠ 4 by decide), rne Rg (show (3 : Fin 10) ≠ 6 by decide), hL]
            · simp [h4, h6, h3]
    · rfl
  | b :: bs, σ, a, w, j, hst, hs, hp, hd, hjc, hL, hLc, hA, hW, hcap, hwM, hT, hU => by
    have v : ∀ i j : Fin 10, i ≠ j → Rg i ≠ Rg j := fun i j h => rne Rg h
    have hpow : 1 ≤ 2 ^ (b :: bs).length := Nat.one_le_two_pow
    have hwM' : w ≤ M := le_trans (Nat.le_mul_of_pos_right w hpow) hwM
    have hbv : bval (b :: bs) = b.toNat + 2 * bval bs := rfl
    have hw2 : w * 2 ^ (b :: bs).length = (w + w) * 2 ^ bs.length := by simp [pow_succ]; ring
    obtain ⟨σ1, e1⟩ : ∃ τ, τ = σ.setv (Rg 3) (σ.val (Rg 3) - 1) := ⟨_, rfl⟩
    have d1 := WExec.dec (cap := cap) (Rg 3) σ (by rw [hL]; exact hLc)
    rw [← e1] at d1
    have g1 : ∀ i : Fin 10, i ≠ 3 → σ1.val (Rg i) = σ.val (Rg i) := fun i hi => by
      rw [e1]; simp [Function.update_apply, v i 3 hi]
    have hb : wbit σ1 E = b := by
      unfold wbit; rw [e1]; simp only [WState.setv_st, WState.setv_sh]; rw [hst, hs]
      exact frame_read c j b _ (by rw [hd]; rfl)
    obtain ⟨σ2, e2⟩ : ∃ τ, τ = if b then σ1.setv (Rg 4) (a + w) else σ1 := ⟨_, rfl⟩
    have d2 : WExec cap (.ifs E (addToW Rg (Rg 4) (Rg 6)) .skip) σ1 σ2 (25 * M + 6) := by
      cases b
      · rw [e2]; exact WExec.mono (WExec.ifsF (by rw [hb]) (WExec.skip _)) (by omega)
      · rw [e2]
        have hab : a + w ≤ cap := by simp [hbv] at hcap; nlinarith
        have := addTo_spec cap Rg (Rg 4) (Rg 6) (v 4 8 (by decide)) (v 6 8 (by decide)) (v 6 9 (by decide)) σ1
          (by rw [g1 8 (by decide), hT]) (by rw [g1 9 (by decide), hU]) (by rw [g1 6 (by decide), hW]; omega)
          (by rw [g1 4 (by decide), g1 6 (by decide), hA, hW]; exact hab)
        rw [g1 4 (by decide), g1 6 (by decide), hA, hW] at this
        exact WExec.ifsT (by rw [hb]) (WExec.mono this (by omega))
    have g2 : ∀ i : Fin 10, i ≠ 4 → σ2.val (Rg i) = σ1.val (Rg i) := fun i h4 => by
      rw [e2]; cases b
      · rfl
      · simp [Function.update_apply, v i 4 h4]
    have a2 : σ2.val (Rg 4) = a + b.toNat * w := by
      rw [e2]; cases b
      · simp [g1 4 (by decide), hA]
      · simp
    have s2 : σ2.st = σ.st ∧ σ2.sh = σ.sh ∧ σ2.cell = σ.cell := by rw [e2, e1]; cases b <;> simp
    have p2 : σ2.val Pc = j := by
      rw [e2, e1]; cases b <;> simp [Function.update_apply, Ne.symm (hPc 3), Ne.symm (hPc 4), hp]
    have hww : w + w ≤ cap := by
      have : (w + w) * 1 ≤ (w + w) * 2 ^ bs.length := Nat.mul_le_mul_left _ Nat.one_le_two_pow
      omega
    have d3 := addTo_spec cap Rg (Rg 6) (Rg 6) (v 6 8 (by decide)) (v 6 8 (by decide)) (v 6 9 (by decide)) σ2
      (by rw [g2 8 (by decide), g1 8 (by decide), hT]) (by rw [g2 9 (by decide), g1 9 (by decide), hU])
      (by rw [g2 6 (by decide), g1 6 (by decide), hW]; omega)
      (by rw [g2 6 (by decide), g1 6 (by decide), hW]; exact hww)
    rw [g2 6 (by decide), g1 6 (by decide), hW] at d3
    obtain ⟨σ3, e3⟩ : ∃ τ, τ = σ2.setv (Rg 6) (w + w) := ⟨_, rfl⟩
    rw [← e3] at d3
    have s3 : σ3.sh E = 2 * j + 1 ∧ σ3.val Pc = j := by
      rw [e3]; refine ⟨by simp [s2.2.1, hs], ?_⟩
      simp [Function.update_apply, Ne.symm (hPc 6), p2]
    have d4 := adv2_spec cap E Pc σ3 j s3.1 s3.2 (by simp at hjc; omega)
    have body : WExec cap (bitNW E Pc Rg) σ (at2 σ3 E Pc (j + 1)) (50 * M + 22) :=
      WExec.mono (WExec.seq d1 (WExec.seq d2 (WExec.seq d3 d4))) (by omega)
    have v4 : ∀ i : Fin 10, (at2 σ3 E Pc (j + 1)).val (Rg i) = σ3.val (Rg i) := fun i =>
      at2_val_ne _ _ _ _ _ (hPc i)
    have f3 : ∀ i : Fin 10, i ≠ 6 → σ3.val (Rg i) = σ2.val (Rg i) := fun i h6 => by
      rw [e3]; simp [Function.update_apply, v i 6 h6]
    have h3st : σ3.st = σ.st := by rw [e3]; simp [s2.1]
    have ih := bitNLoop_spec hPc c rest M hM bs (at2 σ3 E Pc (j + 1)) (a + b.toNat * w) (w + w) (j + 1)
      (by simp [h3st, hst]) (at2_sh_E _ _ _ _) (at2_val_Pc _ _ _ _) (frame_next c j b _ (by rw [hd]; rfl))
      (by simp at hjc; omega)
      (by rw [v4, f3 3 (by decide), g2 3 (by decide), e1]; simp [hL])
      (by simp at hLc; omega) (by rw [v4, f3 4 (by decide), a2]) (by rw [v4, e3]; simp)
      (by rw [hbv] at hcap; nlinarith) (by rw [← hw2]; exact hwM)
      (by rw [v4, f3 8 (by decide), g2 8 (by decide), g1 8 (by decide), hT])
      (by rw [v4, f3 9 (by decide), g2 9 (by decide), g1 9 (by decide), hU])
    refine WExec.cast cap (WExec.whrT (by rw [hL]; simp) body ih) ?_
      (by rw [List.length_cons, Nat.add_mul, Nat.one_mul]; omega)
    have hA' : a + b.toNat * w + (w + w) * bval bs = a + w * bval (b :: bs) := by rw [hbv]; ring
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
      · rw [at2_val_ne _ _ _ _ _ hP, at2_val_ne _ _ _ _ _ hP]; unfold nSt; dsimp only
        by_cases h4 : r = Rg 4
        · rw [if_pos h4, if_pos h4]; exact hA'
        · rw [if_neg h4, if_neg h4]
          by_cases h6 : r = Rg 6
          · rw [if_pos h6, if_pos h6]; exact hw2.symm
          · rw [if_neg h6, if_neg h6]
            by_cases h3 : r = Rg 3
            · rw [if_pos h3, if_pos h3]
            · rw [if_neg h3, if_neg h3, at2_val_ne _ _ _ _ _ hP, e3]
              simp only [WState.setv_val, Function.update_apply, if_neg h6]
              rw [e2, e1]
              cases b <;> simp [Function.update_apply, h4, h3]
    · show σ3.cell = σ.cell
      exact h3c

end NearCubicWires.WireExponent3_5.FinalPass.ThrRead
