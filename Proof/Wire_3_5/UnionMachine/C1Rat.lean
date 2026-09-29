import Proof.Wire_3_5.UnionMachine.C1Rng
import Proof.Wire_3_5.Primitive.Writers.UnaryArith

/-! # C6 front, the C1 dock: a population's weight `p_X = c/2^e` in lowest terms (P3:3395-3399, 1326-1330)

C1's request carries each population's weight as `ratWord p_X` (`Plan.selWord`), and the union's weight is the
incidence ratio `p_X = c_X/(2·2^{cb})` (`UnionGuess.weight`, P3:3395-3399), a dyadic ratio whose lowest terms strip
the common factors of `2`. With `c ≥ 1` and `e` in unary registers:
* **`rstep`**, `rstepN`: halve `c` while it is even (at most `e` times), counting the remaining exponent;
* **`ratWord_dyadic`**: `ratWord (c/2^e) = intWord C ++ natWord (2^D)` for `(C, _, D) = rstepN e (c, false, 0)`;
* **`ratW_spec`**: the register program appends `marks (ratWord (c/2^e))`.

Paper quantity of the main type: the weight `p_X` of a carrier in `star:selection`'s request. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.C1Rat
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.WriteNat
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord intWord)
open NearCubicWires.WireExponent3_5 (ratWord)

/-! ## The reduction -/

/-- One step: halve an even `c` while reducing; otherwise stop and count the exponent. -/
def rstep : ℕ × Bool × ℕ → ℕ × Bool × ℕ
  | (c, false, d) => if c % 2 = 0 then (c / 2, false, d) else (c, true, d + 1)
  | (c, true, d) => (c, true, d + 1)

/-- `k` steps. -/
def rstepN : ℕ → ℕ × Bool × ℕ → ℕ × Bool × ℕ
  | 0, x => x
  | k + 1, x => rstep (rstepN k x)

/-- The invariant after `k` steps from `(c, false, 0)`. -/
structure RInv (c k : ℕ) (x : ℕ × Bool × ℕ) : Prop where
  le : x.2.2 ≤ k
  eq : c = x.1 * 2 ^ (k - x.2.2)
  off : x.2.1 = false → x.2.2 = 0
  odd : x.2.1 = true → x.1 % 2 = 1

theorem rinv (c : ℕ) : ∀ k, RInv c k (rstepN k (c, false, 0))
  | 0 => ⟨le_rfl, by simp [rstepN], fun _ => rfl, fun h => by simp [rstepN] at h⟩
  | k + 1 => by
    have ih := rinv c k
    show RInv c (k + 1) (rstep (rstepN k (c, false, 0)))
    generalize rstepN k (c, false, 0) = x at ih ⊢
    obtain ⟨C, f, d⟩ := x
    cases f with
    | false =>
      have hd : d = 0 := ih.off rfl
      subst hd
      by_cases hC : C % 2 = 0
      · simp only [rstep, hC, if_true]
        refine ⟨Nat.zero_le _, ?_, fun _ => rfl, fun h => by simp at h⟩
        have e1 := ih.eq
        simp only [Nat.sub_zero] at e1 ⊢
        rw [e1, pow_succ]
        have : C = C / 2 * 2 := (Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero hC)).symm
        conv_lhs => rw [this]
        ring
      · simp only [rstep, hC, if_false]
        refine ⟨by simp, ?_, fun h => by simp at h, fun _ => by omega⟩
        have e1 := ih.eq
        simp only [Nat.sub_zero] at e1 ⊢
        rw [e1, show k + 1 - (0 + 1) = k by omega]
    | true =>
      simp only [rstep]
      refine ⟨by have := ih.le; simp only at this ⊢; omega, ?_, fun h => by simp at h, fun _ => ih.odd rfl⟩
      have e1 := ih.eq
      have hle := ih.le
      simp only at e1 hle ⊢
      rw [e1, show k + 1 - (d + 1) = k - d by omega]

theorem coprime_red (c k : ℕ) :
    Nat.Coprime (rstepN k (c, false, 0)).1 (2 ^ (rstepN k (c, false, 0)).2.2) := by
  have hI := rinv c k
  generalize rstepN k (c, false, 0) = x at hI ⊢
  obtain ⟨C, f, d⟩ := x
  cases f with
  | false =>
    have hd : d = 0 := hI.off rfl
    subst hd
    simp
  | true =>
    have ho : C % 2 = 1 := hI.odd rfl
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr ho))

/-- **The dyadic ratio in lowest terms.** -/
theorem ratWord_dyadic (c e : ℕ) :
    ratWord ((c : ℚ) / 2 ^ e) =
      intWord ((rstepN e (c, false, 0)).1 : ℤ) ++ natWord (2 ^ (rstepN e (c, false, 0)).2.2) := by
  have hI := rinv c e
  have hcop := coprime_red c e
  set C := (rstepN e (c, false, 0)).1 with hC
  set D := (rstepN e (c, false, 0)).2.2 with hD
  have hv : (c : ℚ) / 2 ^ e = ((C : ℤ) : ℚ) / ((2 ^ D : ℕ) : ℤ) := by
    have e1 : c = C * 2 ^ (e - D) := hI.eq
    have hle : D ≤ e := hI.le
    rw [e1]
    push_cast
    have h2 : (2 : ℚ) ^ e = 2 ^ (e - D) * 2 ^ D := by rw [← pow_add, Nat.sub_add_cancel hle]
    rw [h2]
    have h3 : (2 : ℚ) ^ (e - D) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hb : (0 : ℤ) < ((2 ^ D : ℕ) : ℤ) := by exact_mod_cast Nat.two_pow_pos D
  have hco : Nat.Coprime ((C : ℤ)).natAbs (((2 ^ D : ℕ) : ℤ)).natAbs := by
    simpa [Int.natAbs_natCast] using hcop
  have hden : (((C : ℤ) : ℚ) / (((2 ^ D : ℕ) : ℤ) : ℚ)).den = 2 ^ D := by
    have := Rat.den_div_eq_of_coprime hb hco
    exact_mod_cast this
  unfold ratWord
  rw [hv, Rat.num_div_eq_of_coprime hb hco, hden]

theorem rstepN_le (c k : ℕ) : (rstepN k (c, false, 0)).1 ≤ c := by
  have h := (rinv c k).eq
  have : 1 ≤ 2 ^ (k - (rstepN k (c, false, 0)).2.2) := Nat.one_le_two_pow
  nlinarith

theorem rstepN_d (c k : ℕ) : (rstepN k (c, false, 0)).2.2 ≤ k := (rinv c k).le

/-! ## The register program -/

section Prog
variable {ns nr : ℕ} (cap : ℕ) (o : Fin (ns + 1)) (R : Fin 8 ↪ Fin nr) (Z : Fin 10 ↪ Fin nr)

/-- `pow2W`'s registers `(D, P, U, T)`. -/
def z4 : Fin 4 ↪ Fin 10 := ⟨![8, 9, 3, 4], by decide⟩

/-- One reduction step on `(C, F, D) = (Z 0, Z 7, Z 8)`; scratch `U T QQ RB = Z 3 … Z 6`. -/
def rbody : WM ns nr :=
  .ifr (Z 7) (.inc (Z 8)) (.seq (FinalPass.Hash4.wcopyR (Z 0) (Z 4) (Z 3)) (.seq (halveM (Z 4) (Z 5) (Z 6))
    (.ifr (Z 6) (.seq (WM.clear (Z 4)) (.seq (.dec (Z 6)) (.seq (.inc (Z 7)) (.inc (Z 8)))))
      (.seq (WM.clear (Z 0)) (WM.move (Z 4) (Z 0))))))

/-- The state carrying `(C, F, D)`. -/
def stR (σ : WState ns nr) (x : ℕ × Bool × ℕ) : WState ns nr :=
  ((σ.setv (Z 0) x.1).setv (Z 7) (if x.2.1 then 1 else 0)).setv (Z 8) x.2.2

theorem rbody_spec (σ : WState ns nr) (h3 : σ.val (Z 3) = 0) (h4 : σ.val (Z 4) = 0) (h5 : σ.val (Z 5) = 0)
    (h6 : σ.val (Z 6) = 0) (x : ℕ × Bool × ℕ) (hc : x.1 + x.2.2 + 2 ≤ cap) :
    WExec cap (rbody Z) (stR Z σ x) (stR Z σ (rstep x)) (60 * x.1 + 60) := by
  have hne : ∀ {i j : Fin 10}, i ≠ j → Z i ≠ Z j := fun h => Z.injective.ne h
  have d04 : Z 0 ≠ Z 4 := hne (by decide)
  have d06 : Z 0 ≠ Z 6 := hne (by decide)
  have d07 : Z 0 ≠ Z 7 := hne (by decide)
  have d08 : Z 0 ≠ Z 8 := hne (by decide)
  have d34 : Z 3 ≠ Z 4 := hne (by decide)
  have d03 : Z 0 ≠ Z 3 := hne (by decide)
  have d45 : Z 4 ≠ Z 5 := hne (by decide)
  have d46 : Z 4 ≠ Z 6 := hne (by decide)
  have d47 : Z 4 ≠ Z 7 := hne (by decide)
  have d48 : Z 4 ≠ Z 8 := hne (by decide)
  have d56 : Z 5 ≠ Z 6 := hne (by decide)
  have d67 : Z 6 ≠ Z 7 := hne (by decide)
  have d68 : Z 6 ≠ Z 8 := hne (by decide)
  have d78 : Z 7 ≠ Z 8 := hne (by decide)
  have d35 : Z 3 ≠ Z 5 := hne (by decide)
  have d36 : Z 3 ≠ Z 6 := hne (by decide)
  have d37 : Z 3 ≠ Z 7 := hne (by decide)
  have d38 : Z 3 ≠ Z 8 := hne (by decide)
  have d05 : Z 0 ≠ Z 5 := hne (by decide)
  have d57 : Z 5 ≠ Z 7 := hne (by decide)
  have d58 : Z 5 ≠ Z 8 := hne (by decide)
  obtain ⟨c, f, d⟩ := x
  simp only at hc
  have hc0 : c ≤ cap := by omega
  have hc2 : c / 2 ≤ cap := by omega
  have hd : d < cap := by omega
  have hone : 0 < cap := by omega
  cases f with
  | true =>
    have hF : (stR Z σ (c, true, d)).val (Z 7) ≠ 0 := by
      simp [stR, Function.update_apply, d78]
    have e1 := WExec.inc (cap := cap) (Z 8) (stR Z σ (c, true, d)) (by simp [stR]; omega)
    refine WExec.mono (WExec.cast cap (WExec.ifrT hF e1) ?_ le_rfl) (by omega)
    simp only [rstep, stR]
    wgen_eq
  | false =>
    obtain ⟨σ0, hσ0⟩ : ∃ τ, τ = stR Z σ (c, false, d) := ⟨_, rfl⟩
    have g : ∀ j, σ0.val j = if j = Z 8 then d else if j = Z 7 then 0 else if j = Z 0 then c else σ.val j := by
      intro j; rw [hσ0]; simp only [stR, WState.setv_val, Function.update_apply, Bool.false_eq_true, if_false]
    have hF : σ0.val (Z 7) = 0 := by rw [g]; simp [d78.symm]
    have v0 : σ0.val (Z 0) = c := by rw [g]; simp [d08, d07]
    have v3 : σ0.val (Z 3) = 0 := by rw [g]; simp [d38, d37, d03.symm, h3]
    have v4 : σ0.val (Z 4) = 0 := by rw [g]; simp [d48, d47, d04.symm, h4]
    have v5 : σ0.val (Z 5) = 0 := by rw [g]; simp [d58, d57, d05.symm, h5]
    have v6 : σ0.val (Z 6) = 0 := by rw [g]; simp [d68, d67, d06.symm, h6]
    rw [← hσ0]
    have e1 := FinalPass.Hash4.wcopyR_spec cap (Z 0) (Z 4) (Z 3) d04 d03 d34.symm σ0 v4 v3 (by rw [v0]; exact hc0)
    rw [v0] at e1
    obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ0.setv (Z 4) c := ⟨_, rfl⟩
    rw [← hσ1] at e1
    have w5 : σ1.val (Z 5) = 0 := by rw [hσ1]; simp [d45.symm, v5]
    have w6 : σ1.val (Z 6) = 0 := by rw [hσ1]; simp [d46.symm, v6]
    have w4 : σ1.val (Z 4) = c := by rw [hσ1]; simp
    have e2 := halveM_spec cap (Z 4) (Z 5) (Z 6) d45 d46 d56 σ1 w5 w6 (by rw [w4]; exact hc0) hone
    rw [w4] at e2
    obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = (σ1.setv (Z 4) (c / 2)).setv (Z 6) (c % 2) := ⟨_, rfl⟩
    rw [← hσ2] at e2
    have u6 : σ2.val (Z 6) = c % 2 := by rw [hσ2]; simp
    have u4 : σ2.val (Z 4) = c / 2 := by rw [hσ2]; simp [d46]
    have u0 : σ2.val (Z 0) = c := by rw [hσ2, hσ1]; simp [d06, d04, v0]
    have u7 : σ2.val (Z 7) = 0 := by rw [hσ2, hσ1]; simp [d67.symm, d47.symm, hF]
    have u8 : σ2.val (Z 8) = d := by
      rw [hσ2, hσ1]; simp only [WState.setv_val, Function.update_apply, if_neg d68.symm, if_neg d48.symm]
      rw [g]; simp
    by_cases hp : c % 2 = 0
    · -- even: C := c/2
      have hR : σ2.val (Z 6) = 0 := by rw [u6, hp]
      have e3 := wclear_spec cap (Z 0) c σ2 u0 (by rw [u0]; exact hc0)
      have y4 : (σ2.setv (Z 0) 0).val (Z 4) = c / 2 := by simp [d04.symm, u4]
      have y0 : (σ2.setv (Z 0) 0).val (Z 0) = 0 := by simp
      have e4 := wmove_spec cap (Z 4) (Z 0) d04.symm (c / 2) (σ2.setv (Z 0) 0) y4 (by rw [y4]; exact hc2)
        (by rw [y4, y0]; omega)
      rw [y4, y0] at e4
      refine WExec.mono (WExec.cast cap (WExec.ifrF hF (WExec.seq e1 (WExec.seq e2 (WExec.ifrF hR
        (WExec.seq e3 e4))))) ?_ le_rfl) (by omega)
      simp only [rstep, hp, if_true]
      rw [hσ2, hσ1, hσ0]
      simp only [stR, Bool.false_eq_true, if_false]
      refine WState.eq rfl rfl ?_ rfl
      funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases hj0 : j = Z 0
      · subst hj0; simp [d04, d06, d07, d08]
      by_cases hj4 : j = Z 4
      · subst hj4; simp [d04.symm, d46, d47, d48, h4]
      by_cases hj6 : j = Z 6
      · subst hj6; simp [d06.symm, d46.symm, d67, d68, h6, hp]
      by_cases hj7 : j = Z 7
      · subst hj7; simp [d07.symm, d47.symm, d67.symm, d78]
      by_cases hj8 : j = Z 8
      · subst hj8; simp [d08.symm, d48.symm, d68.symm, d78.symm]
      simp [hj0, hj4, hj6, hj7, hj8]
    · -- odd: stop
      have hp1 : c % 2 = 1 := by omega
      have hR : σ2.val (Z 6) ≠ 0 := by rw [u6, hp1]; exact one_ne_zero
      have e3 := wclear_spec cap (Z 4) (c / 2) σ2 u4 (by rw [u4]; exact hc2)
      obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = σ2.setv (Z 4) 0 := ⟨_, rfl⟩
      rw [← hσ3] at e3
      have t6 : σ3.val (Z 6) = 1 := by rw [hσ3]; simp [d46.symm, u6, hp1]
      have e4 := WExec.dec (cap := cap) (Z 6) σ3 (by rw [t6]; omega)
      rw [t6] at e4
      obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = σ3.setv (Z 6) (1 - 1) := ⟨_, rfl⟩
      rw [← hσ4] at e4
      have t7 : σ4.val (Z 7) = 0 := by rw [hσ4, hσ3]; simp [d67.symm, d47.symm, u7]
      have e5 := WExec.inc (cap := cap) (Z 7) σ4 (by rw [t7]; exact hone)
      rw [t7] at e5
      obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = σ4.setv (Z 7) (0 + 1) := ⟨_, rfl⟩
      rw [← hσ5] at e5
      have t8 : σ5.val (Z 8) = d := by rw [hσ5, hσ4, hσ3]; simp [d78.symm, d68.symm, d48.symm, u8]
      have e6 := WExec.inc (cap := cap) (Z 8) σ5 (by rw [t8]; exact hd)
      rw [t8] at e6
      refine WExec.mono (WExec.cast cap (WExec.ifrF hF (WExec.seq e1 (WExec.seq e2 (WExec.ifrT hR
        (WExec.seq e3 (WExec.seq e4 (WExec.seq e5 e6))))))) ?_ le_rfl) (by omega)
      simp only [rstep, hp, if_false]
      rw [hσ5, hσ4, hσ3, hσ2, hσ1, hσ0]
      simp only [stR, Bool.false_eq_true, if_false, if_true]
      refine WState.eq (by simp only [WState.setv_sh]) (by simp only [WState.setv_st]) ?_
        (by simp only [WState.setv_cell])
      funext j
      simp only [WState.setv_val, Function.update_apply]
      by_cases hj0 : j = Z 0
      · subst hj0; simp [d04, d06, d07, d08]
      by_cases hj4 : j = Z 4
      · subst hj4; simp [d04.symm, d46, d47, d48, h4]
      by_cases hj6 : j = Z 6
      · subst hj6; simp [d06.symm, d46.symm, d67, d68, h6]
      by_cases hj7 : j = Z 7
      · subst hj7; simp [d07.symm, d47.symm, d67.symm, d78]
      by_cases hj8 : j = Z 8
      · subst hj8; simp [d08.symm, d48.symm, d68.symm, d78.symm]
      simp [hj0, hj4, hj6, hj7, hj8]

theorem stR_setv (σ : WState ns nr) (x : ℕ × Bool × ℕ) (r : Fin nr) (v : ℕ) (h0 : r ≠ Z 0) (h7 : r ≠ Z 7)
    (h8 : r ≠ Z 8) : stR Z (σ.setv r v) x = (stR Z σ x).setv r v := by
  unfold stR
  rw [wsetv_comm _ _ _ h0, wsetv_comm _ _ _ h7, wsetv_comm _ _ _ h8]

/-- **The reduction loop**: `e` steps from `(c, false, 0)` (counter `Z 2`). -/
theorem rloop_spec (σ : WState ns nr) (c e : ℕ) (h0 : σ.val (Z 0) = c) (h2 : σ.val (Z 2) = e)
    (h3 : σ.val (Z 3) = 0) (h4 : σ.val (Z 4) = 0) (h5 : σ.val (Z 5) = 0) (h6 : σ.val (Z 6) = 0)
    (h7 : σ.val (Z 7) = 0) (h8 : σ.val (Z 8) = 0) (hc : c + e + 2 ≤ cap) :
    WExec cap (.whr (Z 2) (.seq (.dec (Z 2)) (rbody Z))) σ ((stR Z σ (rstepN e (c, false, 0))).setv (Z 2) 0)
      (e * (60 * c + 64) + 1) := by
  have hne : ∀ {i j : Fin 10}, i ≠ j → Z i ≠ Z j := fun h => Z.injective.ne h
  have n20 : Z 2 ≠ Z 0 := hne (by decide)
  have n27 : Z 2 ≠ Z 7 := hne (by decide)
  have n28 : Z 2 ≠ Z 8 := hne (by decide)
  set S : ℕ → WState ns nr := fun k => (stR Z σ (rstepN k (c, false, 0))).setv (Z 2) (e - k) with hS
  have hS0 : S 0 = σ := by
    simp only [hS, rstepN, stR, Nat.sub_zero, Bool.false_eq_true, if_false]
    refine WState.eq rfl rfl ?_ rfl
    funext j
    simp only [WState.setv_val, Function.update_apply]
    by_cases hj2 : j = Z 2
    · subst hj2; simp [h2]
    by_cases hj8 : j = Z 8
    · subst hj8; simp [hj2, h8]
    by_cases hj7 : j = Z 7
    · subst hj7; simp [hj2, hj8, h7]
    by_cases hj0 : j = Z 0
    · subst hj0; simp [hj2, hj8, hj7, h0]
    simp [hj2, hj8, hj7, hj0]
  have hloop := UnionMachine.Round.wloop cap (Z 2) (rbody Z) (60 * c + 60) e S
    (fun k _ => by simp [hS])
    (by omega)
    (fun k hk => by
      have hb := rbody_spec cap Z (σ.setv (Z 2) (e - k - 1))
        (by simp [hne (show (3 : Fin 10) ≠ 2 by decide), h3]) (by simp [hne (show (4 : Fin 10) ≠ 2 by decide), h4])
        (by simp [hne (show (5 : Fin 10) ≠ 2 by decide), h5]) (by simp [hne (show (6 : Fin 10) ≠ 2 by decide), h6])
        (rstepN k (c, false, 0)) (by have := rstepN_le c k; have := rstepN_d c k; omega)
      rw [stR_setv Z σ _ (Z 2) _ n20 n27 n28, stR_setv Z σ _ (Z 2) _ n20 n27 n28] at hb
      have eq1 : (S k).setv (Z 2) (e - k - 1) = (stR Z σ (rstepN k (c, false, 0))).setv (Z 2) (e - k - 1) := by
        simp only [hS]; rw [wsetv_setv]
      have eq2 : S (k + 1) = (stR Z σ (rstep (rstepN k (c, false, 0)))).setv (Z 2) (e - k - 1) := by
        simp only [hS, rstepN]; congr 1
      rw [eq1, eq2]
      exact WExec.mono hb (by have := rstepN_le c k; omega))
  rw [hS0] at hloop
  refine WExec.cast cap hloop ?_ (le_of_eq (by ring))
  simp only [hS, Nat.sub_self]

/-- **The weight writer**: `ratWord (c/2^e)` from `C = Z 0` (consumed) and `E = Z 1` (kept). -/
def ratW : WM ns nr :=
  .seq (FinalPass.Hash4.wcopyR (Z 1) (Z 2) (Z 3)) (.seq (.whr (Z 2) (.seq (.dec (Z 2)) (rbody Z)))
    (.seq (emitPair o (R 7) false) (.seq (WM.move (Z 0) (R 0)) (.seq (writeNatM o R) (.seq (WM.clear (R 0))
      (.seq (WM.clear (Z 7)) (.seq (PrimAsm.UnaryArith.pow2W (z4.trans Z)) (.seq (WM.move (Z 9) (R 0))
        (.seq (writeNatM o R) (.seq (WM.clear (R 0)) (WM.clear (Z 8))))))))))))

/-- The weight writer's cost. -/
def ratCost (c e : ℕ) : ℕ :=
  e * (60 * c + 64) + 40 * c + 40 * e + C1Rng.wnCost c + e * (18 * 2 ^ e + 7) + 20 * 2 ^ e +
    C1Rng.wnCost (2 ^ e) + 100

theorem marks_ratWord (c e : ℕ) :
    marks (ratWord ((c : ℚ) / 2 ^ e)) =
      [true, false] ++ marks (natWord (rstepN e (c, false, 0)).1) ++
        marks (natWord (2 ^ (rstepN e (c, false, 0)).2.2)) := by
  rw [ratWord_dyadic]
  simp [intWord, marks_append, marks]

theorem ratW_spec (hZR : ∀ i j, Z i ≠ R j) (σ : WState ns nr) (c e : ℕ) (h0 : σ.val (Z 0) = c)
    (h1 : σ.val (Z 1) = e) (h2 : σ.val (Z 2) = 0) (h3 : σ.val (Z 3) = 0) (h4 : σ.val (Z 4) = 0)
    (h5 : σ.val (Z 5) = 0) (h6 : σ.val (Z 6) = 0) (h7 : σ.val (Z 7) = 0) (h8 : σ.val (Z 8) = 0)
    (h9 : σ.val (Z 9) = 0) (g0 : σ.val (R 0) = 0) (g1 : σ.val (R 1) = 0) (g2 : σ.val (R 2) = 0)
    (g3 : σ.val (R 3) = 0) (g4 : σ.val (R 4) = 0) (g5 : σ.val (R 5) = 0) (g6 : σ.val (R 6) = 0)
    (ho : σ.sh o = (σ.st o).length)
    (hcap : c + e + 2 ^ (e + 1) + σ.val (R 7) + (marks (ratWord ((c : ℚ) / 2 ^ e))).length +
      6 * natBitLength (c + 2 ^ e) + 20 ≤ cap) :
    WExec cap (ratW o R Z) σ ((appendO σ o (R 7) (marks (ratWord ((c : ℚ) / 2 ^ e)))).setv (Z 0) 0)
      (ratCost c e) := by
  have hne : ∀ {i j : Fin 10}, i ≠ j → Z i ≠ Z j := fun h => Z.injective.ne h
  have rne : ∀ {i j : Fin 8}, i ≠ j → R i ≠ R j := fun h => R.injective.ne h
  have hmk := marks_ratWord c e
  have hCc : (rstepN e (c, false, 0)).1 ≤ c := rstepN_le c e
  have hDe : (rstepN e (c, false, 0)).2.2 ≤ e := rstepN_d c e
  obtain ⟨x, hx⟩ : ∃ y, y = rstepN e (c, false, 0) := ⟨_, rfl⟩
  rw [← hx] at hmk hCc hDe
  obtain ⟨C, fC, D⟩ := x
  simp only at hmk hCc hDe
  have hpD : 2 ^ D ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) hDe
  have hpD1 : 2 ^ (D + 1) ≤ 2 ^ (e + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have p0 := Nat.two_pow_pos e
  have p1 := Nat.two_pow_pos D
  rw [hmk] at hcap ⊢
  simp only [List.length_append] at hcap
  have hnC := C1Rng.nbl_mono (show C ≤ c + 2 ^ e by omega)
  have hnP := C1Rng.nbl_mono (show 2 ^ D ≤ c + 2 ^ e by omega)
  have hpe : 2 ^ (e + 1) = 2 * 2 ^ e := by rw [pow_succ]; ring
  -- 1. K := e
  have e1 := FinalPass.Hash4.wcopyR_spec cap (Z 1) (Z 2) (Z 3) (hne (by decide)) (hne (by decide)) (hne (by decide))
    σ h2 h3 (by rw [h1]; omega)
  rw [h1] at e1
  obtain ⟨σ1, hσ1⟩ : ∃ τ, τ = σ.setv (Z 2) e := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have f1 : ∀ j, j ≠ Z 2 → σ1.val j = σ.val j := fun j hj => by rw [hσ1]; simp [hj]
  -- 2. the reduction
  have e2 := rloop_spec cap Z σ1 c e (by rw [f1 _ (hne (by decide)), h0]) (by rw [hσ1]; simp)
    (by rw [f1 _ (hne (by decide)), h3]) (by rw [f1 _ (hne (by decide)), h4]) (by rw [f1 _ (hne (by decide)), h5])
    (by rw [f1 _ (hne (by decide)), h6]) (by rw [f1 _ (hne (by decide)), h7]) (by rw [f1 _ (hne (by decide)), h8])
    (by omega)
  rw [← hx] at e2
  obtain ⟨σ2, hσ2⟩ : ∃ τ, τ = (stR Z σ1 (C, fC, D)).setv (Z 2) 0 := ⟨_, rfl⟩
  rw [← hσ2] at e2
  have f2 : ∀ j, j ≠ Z 0 → j ≠ Z 7 → j ≠ Z 8 → j ≠ Z 2 → σ2.val j = σ.val j := fun j a b d e' => by
    rw [hσ2]; simp only [stR, WState.setv_val, Function.update_apply, e', a, b, d, if_false]; exact f1 j e'
  have f2C : σ2.val (Z 0) = C := by
    rw [hσ2]; simp [stR, hne (show (0 : Fin 10) ≠ 2 by decide), hne (show (0 : Fin 10) ≠ 8 by decide),
      hne (show (0 : Fin 10) ≠ 7 by decide)]
  have f2D : σ2.val (Z 8) = D := by
    rw [hσ2]; simp [stR, hne (show (8 : Fin 10) ≠ 2 by decide)]
  have f2F : σ2.val (Z 7) ≤ 1 := by
    rw [hσ2]; simp only [stR, WState.setv_val, Function.update_apply, if_neg (hne (show (7 : Fin 10) ≠ 2 by decide)),
      if_neg (hne (show (7 : Fin 10) ≠ 8 by decide)), if_pos rfl]; split_ifs <;> omega
  have s2 : σ2.st = σ.st ∧ σ2.sh = σ.sh := by rw [hσ2, hσ1]; exact ⟨rfl, rfl⟩
  -- 3. the sign bit
  have e3 := emitPair_spec cap o (R 7) false σ2 (by rw [s2.1, s2.2]; exact ho)
    (by rw [f2 _ (hZR 0 7).symm (hZR 7 7).symm (hZR 8 7).symm (hZR 2 7).symm]; omega)
  obtain ⟨σ3, hσ3⟩ : ∃ τ, τ = appendO σ2 o (R 7) [true, false] := ⟨_, rfl⟩
  rw [← hσ3] at e3
  have f3 : ∀ j, j ≠ R 7 → σ3.val j = σ2.val j := fun j hj => by rw [hσ3]; simp [hj]
  -- 4. R 0 := C
  have e4 := wmove_spec cap (Z 0) (R 0) (hZR 0 0) C σ3 (by rw [f3 _ (hZR 0 7), f2C])
    (by rw [f3 _ (hZR 0 7), f2C]; omega)
    (by rw [f3 _ (hZR 0 7), f2C, f3 _ (rne (by decide)), f2 _ (hZR 0 0).symm (hZR 7 0).symm (hZR 8 0).symm
      (hZR 2 0).symm, g0]; omega)
  obtain ⟨σ4, hσ4⟩ : ∃ τ, τ = (σ3.setv (Z 0) 0).setv (R 0) (σ3.val (R 0) + σ3.val (Z 0)) := ⟨_, rfl⟩
  rw [← hσ4] at e4
  have v40 : σ4.val (R 0) = C := by
    rw [hσ4]; simp only [WState.setv_val, Function.update_self]
    rw [f3 _ (hZR 0 7), f2C, f3 _ (rne (by decide)), f2 _ (hZR 0 0).symm (hZR 7 0).symm (hZR 8 0).symm
      (hZR 2 0).symm, g0]; omega
  have f4 : ∀ j, j ≠ R 0 → j ≠ Z 0 → σ4.val j = σ3.val j := fun j a b => by rw [hσ4]; simp [a, b]
  have fr : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → σ4.val (R i) = σ.val (R i) := by
    intro i a b
    rw [f4 _ (rne a) (hZR 0 i).symm, f3 _ (rne b), f2 _ (hZR 0 i).symm (hZR 7 i).symm (hZR 8 i).symm (hZR 2 i).symm]
  have s4 : σ4.sh o = (σ4.st o).length := by rw [hσ4, hσ3]; simp [s2.1, s2.2, ho]
  -- 5. natWord C
  have e5 := writeNatM_spec cap o R σ4 (by rw [fr 1 (by decide) (by decide), g1]) (by rw [fr 2 (by decide) (by decide), g2])
    (by rw [fr 3 (by decide) (by decide), g3]) (by rw [fr 4 (by decide) (by decide), g4])
    (by rw [fr 5 (by decide) (by decide), g5]) (by rw [fr 6 (by decide) (by decide), g6]) s4
    (by
      rw [v40, f4 _ (rne (by decide)) (hZR 0 7).symm, hσ3]
      simp only [appendO_val, Function.update_self]
      rw [f2 _ (hZR 0 7).symm (hZR 7 7).symm (hZR 8 7).symm (hZR 2 7).symm]
      simp only [List.length_cons, List.length_nil] at hcap ⊢
      omega)
  rw [v40] at e5
  obtain ⟨σ5, hσ5⟩ : ∃ τ, τ = appendO σ4 o (R 7) (marks (natWord C)) := ⟨_, rfl⟩
  rw [← hσ5] at e5
  have f5 : ∀ j, j ≠ R 7 → σ5.val j = σ4.val j := fun j hj => by rw [hσ5]; simp [hj]
  -- 6. R 0 := 0
  have e6 := wclear_spec cap (R 0) C σ5 (by rw [f5 _ (rne (by decide)), v40]) (by rw [f5 _ (rne (by decide)), v40]; omega)
  obtain ⟨σ6, hσ6⟩ : ∃ τ, τ = σ5.setv (R 0) 0 := ⟨_, rfl⟩
  rw [← hσ6] at e6
  -- 7. F := 0
  have v67 : σ6.val (Z 7) ≤ 1 := by
    rw [hσ6]; simp only [WState.setv_val, Function.update_apply, if_neg (hZR 7 0)]
    rw [f5 _ (hZR 7 7), f4 _ (hZR 7 0) (hne (by decide)), f3 _ (hZR 7 7)]; exact f2F
  have e7 := wclear_spec cap (Z 7) (σ6.val (Z 7)) σ6 rfl (by omega)
  obtain ⟨σ7, hσ7⟩ : ∃ τ, τ = σ6.setv (Z 7) 0 := ⟨_, rfl⟩
  rw [← hσ7] at e7
  -- the values below `σ7`
  have f7 : ∀ j, j ≠ Z 7 → j ≠ R 0 → j ≠ R 7 → j ≠ Z 0 → σ7.val j = σ2.val j := by
    intro j a b d e'
    rw [hσ7, hσ6]; simp only [WState.setv_val, Function.update_apply, a, b, if_false]
    rw [f5 _ d, f4 _ b e', f3 _ d]
  have v78 : σ7.val (Z 8) = D := by
    rw [f7 _ (hne (by decide)) (hZR 8 0) (hZR 8 7) (hne (by decide)), f2D]
  have v79 : σ7.val (Z 9) = 0 := by
    rw [f7 _ (hne (by decide)) (hZR 9 0) (hZR 9 7) (hne (by decide)),
      f2 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), h9]
  have v73 : σ7.val (Z 3) = 0 := by
    rw [f7 _ (hne (by decide)) (hZR 3 0) (hZR 3 7) (hne (by decide)),
      f2 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), h3]
  have v74 : σ7.val (Z 4) = 0 := by
    rw [f7 _ (hne (by decide)) (hZR 4 0) (hZR 4 7) (hne (by decide)),
      f2 _ (hne (by decide)) (hne (by decide)) (hne (by decide)) (hne (by decide)), h4]
  have v70 : σ7.val (R 0) = 0 := by
    rw [hσ7, hσ6]; simp [(hZR 7 0).symm]
  -- 8. P := 2^D
  have e8 := PrimAsm.UnaryArith.pow2W_spec cap (z4.trans Z) σ7 v79 v73 v74 (by
    show 2 ^ (σ7.val (Z 8) + 1) ≤ cap
    rw [v78]; omega)
  have e8' : WExec cap (PrimAsm.UnaryArith.pow2W (z4.trans Z)) σ7 (σ7.setv (Z 9) (2 ^ D))
      (D * (18 * 2 ^ D + 7) + 18 * D + 20) := by
    have t0 : (z4.trans Z) 0 = Z 8 := rfl
    have t1 : (z4.trans Z) 1 = Z 9 := rfl
    rw [t0, t1, v78] at e8
    exact e8
  obtain ⟨σ8, hσ8⟩ : ∃ τ, τ = σ7.setv (Z 9) (2 ^ D) := ⟨_, rfl⟩
  rw [← hσ8] at e8'
  have v89 : σ8.val (Z 9) = 2 ^ D := by rw [hσ8]; simp
  have v80 : σ8.val (R 0) = 0 := by rw [hσ8]; simp [(hZR 9 0).symm, v70]
  -- 9. R 0 := 2^D
  have e9 := wmove_spec cap (Z 9) (R 0) (hZR 9 0) (2 ^ D) σ8 v89 (by rw [v89]; omega) (by rw [v89, v80]; omega)
  obtain ⟨σ9, hσ9⟩ : ∃ τ, τ = (σ8.setv (Z 9) 0).setv (R 0) (σ8.val (R 0) + σ8.val (Z 9)) := ⟨_, rfl⟩
  rw [← hσ9] at e9
  have v90 : σ9.val (R 0) = 2 ^ D := by rw [hσ9]; simp [v89, v80]
  have f9 : ∀ j, j ≠ R 0 → j ≠ Z 9 → j ≠ Z 7 → j ≠ R 7 → j ≠ Z 0 → σ9.val j = σ2.val j := by
    intro j a b d e' g'
    rw [hσ9]; simp only [WState.setv_val, Function.update_apply, a, b, if_false]
    rw [hσ8]; simp only [WState.setv_val, Function.update_apply, b, if_false]
    exact f7 j d a e' g'
  have fr9 : ∀ i : Fin 8, i ≠ 0 → i ≠ 7 → σ9.val (R i) = σ.val (R i) := by
    intro i a b
    rw [f9 _ (rne a) (hZR 9 i).symm (hZR 7 i).symm (rne b) (hZR 0 i).symm,
      f2 _ (hZR 0 i).symm (hZR 7 i).symm (hZR 8 i).symm (hZR 2 i).symm]
  have v97 : σ9.val (R 7) = σ.val (R 7) + 2 + (marks (natWord C)).length := by
    rw [hσ9, hσ8, hσ7, hσ6]
    simp only [WState.setv_val, Function.update_apply, if_neg (rne (show (7 : Fin 8) ≠ 0 by decide)),
      if_neg (hZR 9 7).symm, if_neg (hZR 7 7).symm]
    rw [hσ5]; simp only [appendO_val, Function.update_self]
    rw [f4 _ (rne (by decide)) (hZR 0 7).symm, hσ3]; simp only [appendO_val, Function.update_self]
    rw [f2 _ (hZR 0 7).symm (hZR 7 7).symm (hZR 8 7).symm (hZR 2 7).symm]
    simp
  have s9 : σ9.sh o = (σ9.st o).length := by
    rw [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3]; simp [s2.1, s2.2, ho]; omega
  -- 10. natWord (2^D)
  have e10 := writeNatM_spec cap o R σ9 (by rw [fr9 1 (by decide) (by decide), g1])
    (by rw [fr9 2 (by decide) (by decide), g2]) (by rw [fr9 3 (by decide) (by decide), g3])
    (by rw [fr9 4 (by decide) (by decide), g4]) (by rw [fr9 5 (by decide) (by decide), g5])
    (by rw [fr9 6 (by decide) (by decide), g6]) s9 (by
      rw [v90, v97]; simp only [List.length_cons, List.length_nil] at hcap; omega)
  rw [v90] at e10
  obtain ⟨σ10, hσ10⟩ : ∃ τ, τ = appendO σ9 o (R 7) (marks (natWord (2 ^ D))) := ⟨_, rfl⟩
  rw [← hσ10] at e10
  -- 11, 12. R 0 := 0, D := 0
  have e11 := wclear_spec cap (R 0) (2 ^ D) σ10 (by rw [hσ10]; simp [rne (show (0 : Fin 8) ≠ 7 by decide), v90])
    (by rw [hσ10]; simp [rne (show (0 : Fin 8) ≠ 7 by decide), v90]; omega)
  obtain ⟨σ11, hσ11⟩ : ∃ τ, τ = σ10.setv (R 0) 0 := ⟨_, rfl⟩
  rw [← hσ11] at e11
  have v118 : σ11.val (Z 8) = D := by
    rw [hσ11, hσ10]; simp only [WState.setv_val, appendO_val, Function.update_apply, if_neg (hZR 8 0),
      if_neg (hZR 8 7)]
    rw [f9 _ (hZR 8 0) (hne (by decide)) (hne (by decide)) (hZR 8 7) (hne (by decide)), f2D]
  have e12 := wclear_spec cap (Z 8) D σ11 v118 (by rw [v118]; omega)
  refine WExec.mono (WExec.cast cap (WExec.seq e1 (WExec.seq e2 (WExec.seq e3 (WExec.seq e4 (WExec.seq e5
    (WExec.seq e6 (WExec.seq e7 (WExec.seq e8' (WExec.seq e9 (WExec.seq e10 (WExec.seq e11 e12))))))))))) ?_ le_rfl) ?_
  · -- the final state
    have v99 : σ9.val (Z 9) = 0 := by rw [hσ9]; simp [hZR 9 0]
    have v977 : σ9.val (Z 7) = 0 := by
      rw [hσ9, hσ8, hσ7]; simp [hZR 7 0, hne (show (7 : Fin 10) ≠ 9 by decide)]
    have v900 : σ9.val (Z 0) = 0 := by
      rw [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4]
      simp [hZR 0 0, hZR 0 7, hne (show (0 : Fin 10) ≠ 9 by decide), hne (show (0 : Fin 10) ≠ 7 by decide)]
    have st9 : σ9.st = σ5.st := by rw [hσ9, hσ8, hσ7, hσ6]; rfl
    have sh9 : σ9.sh = σ5.sh := by rw [hσ9, hσ8, hσ7, hσ6]; rfl
    have st5 : σ5.st = Function.update σ.st o (σ.st o ++ [true, false] ++ marks (natWord C)) := by
      rw [hσ5, hσ4, hσ3]; funext j; by_cases hj : j = o
      · subst hj; simp [s2.1]
      · simp [hj, s2.1]
    have sh5 : σ5.sh = Function.update σ.sh o (σ.sh o + 2 + (marks (natWord C)).length) := by
      rw [hσ5, hσ4, hσ3]; funext j; by_cases hj : j = o
      · subst hj; simp [s2.2]
      · simp [hj, s2.2]
    have c9 : σ9.cell = σ.cell := by rw [hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, hσ2, hσ1]; rfl
    rw [hσ11, hσ10]
    refine WState.eq ?_ ?_ ?_ ?_
    · funext j
      by_cases hj : j = o
      · subst hj; simp [sh9, sh5]; omega
      · simp [hj, sh9, sh5]
    · funext j
      by_cases hj : j = o
      · subst hj; simp [st9, st5]
      · simp [hj, st9, st5]
    · funext j
      simp only [WState.setv_val, appendO_val, Function.update_apply]
      by_cases a8 : j = Z 8
      · subst a8; simp [hZR 8 0, hZR 8 7, hne (show (8 : Fin 10) ≠ 0 by decide), h8]
      by_cases a0 : j = R 0
      · subst a0; simp [(hZR 8 0).symm, (hZR 0 0).symm, rne (show (0 : Fin 8) ≠ 7 by decide), g0]
      by_cases a7 : j = R 7
      · subst a7
        simp only [a8, a0, if_false, if_true, (hZR 0 7).symm, v97, List.length_append, List.length_cons,
          List.length_nil]
        omega
      simp only [a8, a0, a7, if_false]
      by_cases a9 : j = Z 9
      · subst a9; simp [hne (show (9 : Fin 10) ≠ 0 by decide), v99, h9]
      by_cases a77 : j = Z 7
      · subst a77; simp [hne (show (7 : Fin 10) ≠ 0 by decide), v977, h7]
      by_cases a00 : j = Z 0
      · subst a00; simp [v900]
      simp only [a00, if_false]
      by_cases a2 : j = Z 2
      · subst a2
        rw [f9 _ (hZR 2 0) (hne (by decide)) (hne (by decide)) (hZR 2 7) (hne (by decide)), hσ2]; simp [h2]
      rw [f9 j a0 a9 a77 a7 a00]
      exact f2 j a00 a77 a8 a2
    · simp [c9]
  · unfold ratCost
    have hw1 := C1Rng.wnCost_mono hCc
    have hw2 := C1Rng.wnCost_mono hpD
    have hm : D * (18 * 2 ^ D + 7) ≤ e * (18 * 2 ^ e + 7) := Nat.mul_le_mul hDe (by omega)
    have hm2 : e * (60 * c + 64) ≥ 0 := Nat.zero_le _
    have hwc : C1Rng.wnCost C = (natBitLength C + 10) * (100 * C + 200) := rfl
    have hwp : C1Rng.wnCost (2 ^ D) = (natBitLength (2 ^ D) + 10) * (100 * 2 ^ D + 200) := rfl
    have hf7 : σ6.val (Z 7) ≤ 1 := v67
    have p2 := Nat.two_pow_pos e
    have p3 := Nat.two_pow_pos D
    rw [← hwc, ← hwp]
    generalize e * (60 * c + 64) = A at *
    generalize D * (18 * 2 ^ D + 7) = B at *
    generalize e * (18 * 2 ^ e + 7) = B' at *
    generalize 2 ^ D = P at *
    generalize 2 ^ e = P' at *
    omega

end Prog

end NearCubicWires.WireExponent3_5.UnionMachine.C1Rat
