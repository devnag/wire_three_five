import Proof.Wire_3_5.FinalPass.FreeGen8
import Proof.Wire_3_5.Primitive.SeedFix.C4CapD

/-! # The free numbers, v2, part 4: the bounds

C4.K's generic bounds for `freeProg2 κ` in the forms of `C4SymW.SymFreeOk6` (the capacity `2^{⌊n/8⌋ + O(1)}`): the capacity
`need + need2 ≤ Ko·2^{⌊n/8⌋}` and the values but `ρ` below it on every small `x` (the `(B+1)²` terms absorbed by
`c·(B+1)² ≤ n/16 + K₀`, `C4Cap.capExp_le_half`), the steps `≤ K(cap+1)²`, `ρ` polynomial in `n`, the pad `2^ρ`
within the table and selection classes (P3:3098-3100; `ρ` is FreeGen's).
* `need2K`, `need2D`, **`need2_le`**, `bsq_le_n16`, `val2_le_need`, **`ok2_le`**, **`cost2_le`**, **`val2_le`**,
  **`rho2_le`**, **`pad2`**.
Paper quantities of the main types: the capacity and the values of the free numbers against `2^{⌊n/8⌋}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires NearCubicWires.WireExponent3_5.PrimT.C4Set

/-- The v2 capacity's coefficient. -/
def need2K (κ : FreeK2) : ℕ := needK κ.base + (13 + 4 * κ.k.dQ + 2 * κ.k.dH + 2 * κ.k.dP + needK κ.base + κ.m0)

/-- The v2 capacity's exponent of `(B+1)²`. -/
def need2D (κ : FreeK2) (Ds : ℕ) : ℕ := needD κ.base Ds + Ds + κ.eH + κ.eP + κ.k.dC + 2

theorem mOf_le_need (κ : FreeK) (x : FreeIn) : mOf κ x ≤ need κ x := by
  unfold mOf need
  generalize κ.mA * x.nc + κ.mB * (x.a * W x) + κ.mC * W x + κ.mD * x.a + κ.mF * x.M + κ.mE = Z
  generalize 2 ^ (κ.dC * (β x * β x) + 1) = P
  omega

theorem succ_pow_le (n e : ℕ) : (n + 1) ^ e ≤ 2 ^ (e * (natBitLength n + 1) ^ 2) := by
  have h1 : n + 1 ≤ 2 ^ natBitLength n := n_lt_B n
  have h2 : natBitLength n ≤ (natBitLength n + 1) ^ 2 := by nlinarith
  calc (n + 1) ^ e ≤ (2 ^ natBitLength n) ^ e := Nat.pow_le_pow_left h1 e
    _ = 2 ^ (e * natBitLength n) := by rw [← pow_mul, Nat.mul_comm]
    _ ≤ 2 ^ (e * (natBitLength n + 1) ^ 2) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ h2)

/-- **The v2 capacity is `2^{O((B+1)²) + ⌊n/16⌋}`** on every small `x`. -/
theorem need2_le (κ : FreeK2) (Ds : ℕ) (x : FreeIn) (hs : FreeSmall Ds x) :
    need κ.base x + need2 κ x ≤ need2K κ * 2 ^ (need2D κ Ds * (natBitLength x.n + 1) ^ 2 + x.n / 16) := by
  have h0 := need_le κ.base Ds x hs
  have hm := (mOf_le_need κ.base x).trans h0
  have hkh := hs.1
  have hB := beta_le_B x
  have hn := n_lt_B x.n
  have hH := succ_pow_le x.n κ.eH
  have hP := succ_pow_le x.n κ.eP
  have h16 : x.n / 2 / 2 / 2 / 2 = x.n / 16 := by omega
  obtain ⟨s, hsd⟩ : ∃ s, s = (natBitLength x.n + 1) ^ 2 := ⟨_, rfl⟩
  rw [← hsd] at h0 hm hkh hH hP ⊢
  have hs1 : natBitLength x.n + 1 ≤ s := by rw [hsd]; nlinarith
  have hbb : β x * β x ≤ s := by rw [hsd, sq]; exact Nat.mul_le_mul hB hB
  obtain ⟨E, hEd⟩ : ∃ E, E = need2D κ Ds := ⟨_, rfl⟩
  rw [← hEd]
  have hU : ∀ e, e ≤ E → 2 ^ (e * s) ≤ 2 ^ (E * s + x.n / 16) := fun e he =>
    Nat.pow_le_pow_right (by norm_num) (by have := Nat.mul_le_mul_right s he; omega)
  have gD := hU (needD κ.base Ds) (by rw [hEd]; unfold need2D; omega)
  have gS := hU Ds (by rw [hEd]; unfold need2D; omega)
  have gH := hU κ.eH (by rw [hEd]; unfold need2D; omega)
  have gP := hU κ.eP (by rw [hEd]; unfold need2D; omega)
  have g1 := hU 1 (by rw [hEd]; unfold need2D; omega)
  have gC : 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) ≤ 2 ^ (E * s + x.n / 16) :=
    Nat.pow_le_pow_right (by norm_num) (by
      have : κ.k.dC * (β x * β x) ≤ E * s := Nat.mul_le_mul (by rw [hEd]; unfold need2D; omega) hbb
      omega)
  have gC' : 2 ^ (κ.k.dC * (β x * β x)) ≤ 2 ^ (E * s + x.n / 16) :=
    Nat.pow_le_pow_right (by norm_num) (by
      have : κ.k.dC * (β x * β x) ≤ E * s := Nat.mul_le_mul (by rw [hEd]; unfold need2D; omega) hbb
      omega)
  have hsl : natBitLength x.n + 1 ≤ 1 * s := by omega
  have hb2 : 2 ^ (natBitLength x.n + 1) ≤ 2 ^ (1 * s) := Nat.pow_le_pow_right (by norm_num) hsl
  have hbl : natBitLength x.n + 1 < 2 ^ (natBitLength x.n + 1) := Nat.lt_two_pow_self
  have hn2 : x.n + 2 ≤ 2 ^ (natBitLength x.n + 1) := by rw [pow_succ]; omega
  unfold need2
  rw [h16]
  generalize 2 ^ (E * s + x.n / 16) = U at gD gS gH gP g1 gC gC' ⊢
  generalize 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) = UC at gC ⊢
  generalize 2 ^ (κ.k.dC * (β x * β x)) = UC' at gC' ⊢
  generalize 2 ^ (1 * s) = U1 at g1 hb2 ⊢
  generalize 2 ^ (natBitLength x.n + 1) = V at hb2 hbl hn2
  generalize 2 ^ (needD κ.base Ds * s) = UD at h0 hm gD
  generalize 2 ^ (Ds * s) = US at hkh gS
  generalize 2 ^ (κ.eH * s) = UH at hH gH
  generalize 2 ^ (κ.eP * s) = UP at hP gP
  have hK : needK κ.base * UD ≤ needK κ.base * U := Nat.mul_le_mul_left _ gD
  have t1 : κ.k.dQ * (x.kh + x.kh + β x) ≤ κ.k.dQ * (3 * U) := Nat.mul_le_mul_left _ (by omega)
  have t2 : κ.k.dH * (x.n + 1) ^ κ.eH ≤ κ.k.dH * U := Nat.mul_le_mul_left _ (by omega)
  have t3 : κ.k.dP * (x.n + 1) ^ κ.eP ≤ κ.k.dP * U := Nat.mul_le_mul_left _ (by omega)
  have hU1 : 1 ≤ U := by omega
  have t4 : κ.k.dQ ≤ κ.k.dQ * U := Nat.le_mul_of_pos_right _ hU1
  have t5 : κ.k.dH ≤ κ.k.dH * U := Nat.le_mul_of_pos_right _ hU1
  have t6 : κ.k.dP ≤ κ.k.dP * U := Nat.le_mul_of_pos_right _ hU1
  have t7 : κ.m0 ≤ κ.m0 * U := Nat.le_mul_of_pos_right _ hU1
  have e : need2K κ * U = needK κ.base * U + (13 * U + κ.k.dQ * (3 * U) + κ.k.dQ * U + 2 * (κ.k.dH * U) +
      2 * (κ.k.dP * U) + needK κ.base * U + κ.m0 * U) := by unfold need2K; ring
  rw [e]
  omega

/-- `c·(B+1)² ≤ ⌊n/16⌋ + K₀` (from `C4Cap.capExp_le_half` at `8c`). -/
theorem bsq_le_n16 (c : ℕ) : ∃ K0 : ℕ, ∀ n : ℕ, c * (natBitLength n + 1) ^ 2 ≤ n / 16 + K0 := by
  obtain ⟨K0, hK0⟩ := PrimT.C4Cap.capExp_le_half (8 * c)
  refine ⟨K0 + 1, fun n => ?_⟩
  have h := hK0 n
  rw [Nat.mul_assoc] at h
  omega

theorem val2_le_need (κ : FreeK2) (x : FreeIn) (j : Fin 7) (hj : j.val ≠ 6) :
    freeVal2 κ x j ≤ need κ.base x + need2 κ x := by
  have h0 := val_le_need κ.base x 0 (by decide)
  have hm := mOf_le_need κ.base x
  have hmm : mOf κ.k x = mOf κ.base x := rfl
  have h16 : x.n / 2 / 2 / 2 / 2 = x.n / 16 := by omega
  unfold need2
  rw [h16]
  generalize need κ.base x = N at h0 hm ⊢
  generalize mOf κ.base x = Mo at hm hmm ⊢
  fin_cases j
  · simp [freeVal2, freeVal, FreeK2.base] at h0 ⊢
    generalize 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) = UC
    generalize 2 ^ (κ.k.dC * (β x * β x)) = UC'
    omega
  · simp [freeVal2]
    generalize 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) = UC
    generalize 2 ^ (κ.k.dC * (β x * β x)) = UC'
    omega
  · simp [freeVal2]
    generalize 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) = UC
    generalize 2 ^ (κ.k.dC * (β x * β x)) = UC'
    omega
  · simp [freeVal2]
    generalize 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) = UC
    generalize 2 ^ (κ.k.dC * (β x * β x)) = UC'
    omega
  · simp [freeVal2]; rw [hmm]
    generalize 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) = UC
    generalize 2 ^ (κ.k.dC * (β x * β x)) = UC'
    omega
  · simp [freeVal2]
    generalize 2 ^ (x.n / 16 + κ.k.dC * (β x * β x)) = UC
    generalize 2 ^ (κ.k.dC * (β x * β x)) = UC'
    omega
  · exact absurd rfl hj

theorem cap_bound (κ : FreeK2) (Ds : ℕ) : ∃ Ko : ℕ, ∀ x : FreeIn, FreeSmall Ds x →
    need κ.base x + need2 κ x ≤ Ko * 2 ^ (x.n / 8) := by
  obtain ⟨K0, hK0⟩ := bsq_le_n16 (need2D κ Ds)
  refine ⟨need2K κ * 2 ^ K0, fun x hs => (need2_le κ Ds x hs).trans ?_⟩
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  rw [← pow_add]
  exact Nat.pow_le_pow_right (by norm_num) (by have := hK0 x.n; omega)

/-- **`ok_le`** at `freeProg2 κ` (v5: the capacity `Ko·2^{⌊n/8⌋}`). -/
theorem ok2_le (κ : FreeK2) : ∀ Ds : ℕ, ∃ Ko : ℕ, ∀ (cap : ℕ) (x : FreeIn), FreeSmall Ds x →
    Ko * 2 ^ (x.n / 8) ≤ cap → (freeProg2 κ).ok cap x := fun Ds => by
  obtain ⟨Ko, hKo⟩ := cap_bound κ Ds
  exact ⟨Ko, fun _ x hs hc => (hKo x hs).trans hc⟩

/-- **`cost_le`** at `freeProg2 κ` (v6: `Kc·(cap+1)²`). -/
theorem cost2_le (κ : FreeK2) : ∃ Kc : ℕ, ∀ (cap : ℕ) (x : FreeIn), (freeProg2 κ).cost cap x ≤ Kc * (cap + 1) ^ 2 :=
  ⟨(201 + fixN κ) * 800, fun cap _ => by
    show (201 + fixN κ) * PrimAsm.UnaryPow.sq cap ≤ (201 + fixN κ) * 800 * (cap + 1) ^ 2
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    unfold PrimAsm.UnaryPow.sq
    nlinarith⟩

/-- **`val_le`** at `freeProg2 κ` (v5). -/
theorem val2_le (κ : FreeK2) : ∀ Ds : ℕ, ∃ Kv : ℕ, ∀ (x : FreeIn) (j : Fin 7), FreeSmall Ds x → j.val ≠ 6 →
    (freeProg2 κ).val x j ≤ Kv * 2 ^ (x.n / 8) := fun Ds => by
  obtain ⟨Ko, hKo⟩ := cap_bound κ Ds
  exact ⟨Ko, fun x j hs hj => (val2_le_need κ x j hj).trans (hKo x hs)⟩

/-- **`rho_le`** at `freeProg2 κ`. -/
theorem rho2_le (κ : FreeK2) : ∃ Kr Dr : ℕ, ∀ x : FreeIn, (freeProg2 κ).val x 6 ≤ Kr * (x.n + 1) ^ Dr :=
  ⟨4 * (1 + κ.k.dA + κ.k.dR), 2, fun x => rho_le' κ.k x⟩

/-- **The pad** at `freeProg2 κ` (FreeGen's `ρ`). -/
theorem pad2 (κ : FreeK2) (x : FreeIn) :
    2 ^ (freeProg2 κ).val x 6 ≤ (4 ^ κ.k.dA + 1) * (2 ^ (x.n - (x.kh + x.kh)) * (x.n + 1) ^ (κ.k.dA + κ.k.dR) +
      2 ^ (x.n / 2) * 2 ^ ((κ.k.dA + κ.k.dR) * (natBitLength x.n + 1) ^ 2)) :=
  padX' κ.k x

end NearCubicWires.WireExponent3_5.FinalPass.FreeGen

