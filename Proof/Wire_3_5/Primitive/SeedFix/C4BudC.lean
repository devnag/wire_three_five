import Proof.Wire_3_5.Primitive.SeedFix.C4BudB

/-! # C4.K item (h), part 3: the stage's steps within `c₄·seedClasses E₄` (generic)

P3:3098-3100, 3105-3115: the seed-fixing budget `c₄·seedClasses E₄ q k ψ` (`selection + preprocessing + 2·table`), the
envelope `E₄` fixed before `F`, `c₄` after. From the split of `wrap_split`: the part of rate `7/8` falls below
`2^{c + K₀}·2^{n−k}` (`ex_final`); the table-rate part `(32ℓ + 34)(2^{d₂} + 2^ρ)`, with `ℓ ≤ K_ℓ(n+1)`, `d₂ ≤ n − k + 1`
and the pad `2^ρ ≤ K_p(2^{n−k}(n+1)^{D_p} + 2^{n/2}·2^{D_p(B+1)²})`, falls below `2^{n−k}·n^{A_table}` times a constant
once `D_p + 1 ≤ A_table`; the compiler writer's `B₃ ≤ c_W·2^{c_ψ^W ψ}n^{A^W_pre}` below the preprocessing class once
`E₄ ≥ E_W` there.

* **`budget_le`**.

Paper quantity of the main type: the SYM stage's steps against the seed-fixing budget. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Bud
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost

/-- **The stage's steps within the seed-fixing budget.** -/
theorem budget_le (E₄ EW : Envelope) (n k psi total R ell d2 ρ B3 cR K0 Kl Kp Dp K1 K2 cW : ℕ) (hn : 1 ≤ n)
    (htot : total ≤ R + (32 * ell + 34) * (2 ^ d2 + 2 ^ ρ) + B3) (hR : Ex n 7 cR R) (hk : k ≤ n / 16 + K0)
    (hkn : k ≤ n) (hl : ell ≤ Kl * (n + 1)) (hd2 : d2 ≤ n - k + 1)
    (hρ : 2 ^ ρ ≤ Kp * (2 ^ (n - k) * (n + 1) ^ Dp + 2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2)))
    (hK1 : Dp * (natBitLength n + 1) ^ 2 ≤ n / 16 + K1) (hK2 : n + 1 ≤ 2 ^ (n / 8 + K2))
    (hB3 : B3 ≤ cW * classBound EW .preprocessing n k psi)
    (hEc : EW.cpsi ≤ E₄.cpsi) (hEa : EW.Apre ≤ E₄.Apre) (hAt : Dp + 1 ≤ E₄.Atable) :
    total ≤ (2 ^ (cR + K0) + (32 * Kl + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + K2 + 1)) + cW) *
      PrimAsm.Plan.seedClasses E₄ n k psi := by
  -- the classes
  set tab := 2 ^ (n - k) * n ^ E₄.Atable with htab
  have hsc : tab + classBound E₄ .preprocessing n k psi ≤ PrimAsm.Plan.seedClasses E₄ n k psi := by
    have ht : classBound E₄ .table n k psi = tab := rfl
    unfold PrimAsm.Plan.seedClasses
    omega
  have hn1 : 1 ≤ n ^ E₄.Atable := Nat.one_le_pow _ _ hn
  have htab1 : 2 ^ (n - k) ≤ tab := Nat.le_mul_of_pos_right _ hn1
  -- the rate-7/8 part
  have e1 : R ≤ 2 ^ (cR + K0) * tab := le_trans (ex_final hR hk) (Nat.mul_le_mul_left _ htab1)
  -- the pad's second summand
  have e2 : (n + 1) * (2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2)) ≤ 2 ^ (K0 + K1 + K2 + 1) * 2 ^ (n - k) := by
    calc (n + 1) * (2 ^ (n / 2) * 2 ^ (Dp * (natBitLength n + 1) ^ 2))
        ≤ 2 ^ (n / 8 + K2) * (2 ^ (n / 2) * 2 ^ (n / 16 + K1)) :=
          Nat.mul_le_mul hK2 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hK1))
      _ = 2 ^ (n / 8 + K2 + (n / 2 + (n / 16 + K1))) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (K0 + K1 + K2 + 1 + (n - k)) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2 ^ (K0 + K1 + K2 + 1) * 2 ^ (n - k) := by rw [pow_add]
  -- the table-rate part
  have hpoly : (n + 1) ^ (Dp + 1) ≤ 2 ^ (Dp + 1) * n ^ E₄.Atable := by
    calc (n + 1) ^ (Dp + 1) ≤ (2 * n) ^ (Dp + 1) := Nat.pow_le_pow_left (by omega) _
      _ = 2 ^ (Dp + 1) * n ^ (Dp + 1) := by rw [mul_pow]
      _ ≤ 2 ^ (Dp + 1) * n ^ E₄.Atable := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hn hAt)
  have hd : 2 ^ d2 ≤ 2 * 2 ^ (n - k) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have e3 : (32 * ell + 34) * (2 ^ d2 + 2 ^ ρ) ≤
      (32 * Kl + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + K2 + 1)) * tab := by
    have hl' : 32 * ell + 34 ≤ (32 * Kl + 34) * (n + 1) := by nlinarith
    have hsum : (n + 1) * (2 ^ d2 + 2 ^ ρ) ≤ ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + K2 + 1)) * tab := by
      have a1 : (n + 1) * 2 ^ d2 ≤ 2 * ((n + 1) ^ (Dp + 1) * 2 ^ (n - k)) := by
        have : n + 1 ≤ (n + 1) ^ (Dp + 1) := Nat.le_self_pow (by omega) _
        calc (n + 1) * 2 ^ d2 ≤ (n + 1) ^ (Dp + 1) * (2 * 2 ^ (n - k)) := Nat.mul_le_mul this hd
          _ = 2 * ((n + 1) ^ (Dp + 1) * 2 ^ (n - k)) := by ring
      have a2 : (n + 1) * 2 ^ ρ ≤ Kp * ((n + 1) ^ (Dp + 1) * 2 ^ (n - k)) +
          Kp * (2 ^ (K0 + K1 + K2 + 1) * 2 ^ (n - k)) := by
        calc (n + 1) * 2 ^ ρ ≤ (n + 1) * (Kp * (2 ^ (n - k) * (n + 1) ^ Dp + 2 ^ (n / 2) *
            2 ^ (Dp * (natBitLength n + 1) ^ 2))) := Nat.mul_le_mul_left _ hρ
          _ = Kp * ((n + 1) ^ (Dp + 1) * 2 ^ (n - k)) + Kp * ((n + 1) * (2 ^ (n / 2) *
              2 ^ (Dp * (natBitLength n + 1) ^ 2))) := by ring
          _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ e2) _
      have a3 : (n + 1) ^ (Dp + 1) * 2 ^ (n - k) ≤ 2 ^ (Dp + 1) * tab := by
        rw [htab]
        calc (n + 1) ^ (Dp + 1) * 2 ^ (n - k) ≤ 2 ^ (Dp + 1) * n ^ E₄.Atable * 2 ^ (n - k) :=
              Nat.mul_le_mul_right _ hpoly
          _ = 2 ^ (Dp + 1) * (2 ^ (n - k) * n ^ E₄.Atable) := by ring
      have a4 : 2 ^ (K0 + K1 + K2 + 1) * 2 ^ (n - k) ≤ 2 ^ (K0 + K1 + K2 + 1) * tab := Nat.mul_le_mul_left _ htab1
      calc (n + 1) * (2 ^ d2 + 2 ^ ρ) = (n + 1) * 2 ^ d2 + (n + 1) * 2 ^ ρ := by ring
        _ ≤ 2 * ((n + 1) ^ (Dp + 1) * 2 ^ (n - k)) + (Kp * ((n + 1) ^ (Dp + 1) * 2 ^ (n - k)) +
            Kp * (2 ^ (K0 + K1 + K2 + 1) * 2 ^ (n - k))) := Nat.add_le_add a1 a2
        _ = (2 + Kp) * ((n + 1) ^ (Dp + 1) * 2 ^ (n - k)) + Kp * (2 ^ (K0 + K1 + K2 + 1) * 2 ^ (n - k)) := by ring
        _ ≤ (2 + Kp) * (2 ^ (Dp + 1) * tab) + Kp * (2 ^ (K0 + K1 + K2 + 1) * tab) :=
            Nat.add_le_add (Nat.mul_le_mul_left _ a3) (Nat.mul_le_mul_left _ a4)
        _ = _ := by ring
    calc (32 * ell + 34) * (2 ^ d2 + 2 ^ ρ) ≤ (32 * Kl + 34) * (n + 1) * (2 ^ d2 + 2 ^ ρ) :=
          Nat.mul_le_mul_right _ hl'
      _ = (32 * Kl + 34) * ((n + 1) * (2 ^ d2 + 2 ^ ρ)) := by ring
      _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ hsum
  -- the compiler writer
  have e4 : B3 ≤ cW * classBound E₄ .preprocessing n k psi := by
    refine le_trans hB3 (Nat.mul_le_mul_left _ ?_)
    show 2 ^ (EW.cpsi * psi) * n ^ EW.Apre ≤ 2 ^ (E₄.cpsi * psi) * n ^ E₄.Apre
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hEc))
      (Nat.pow_le_pow_right hn hEa)
  -- together
  set X := (32 * Kl + 34) * ((2 + Kp) * 2 ^ (Dp + 1) + Kp * 2 ^ (K0 + K1 + K2 + 1)) with hX
  have hpre := classBound E₄ .preprocessing n k psi
  calc total ≤ R + (32 * ell + 34) * (2 ^ d2 + 2 ^ ρ) + B3 := htot
    _ ≤ 2 ^ (cR + K0) * tab + X * tab + cW * classBound E₄ .preprocessing n k psi :=
        Nat.add_le_add (Nat.add_le_add e1 e3) e4
    _ ≤ (2 ^ (cR + K0) + X + cW) * (tab + classBound E₄ .preprocessing n k psi) := by
        nlinarith [Nat.zero_le (2 ^ (cR + K0) * classBound E₄ .preprocessing n k psi),
          Nat.zero_le (X * classBound E₄ .preprocessing n k psi), Nat.zero_le (cW * tab)]
    _ ≤ _ := Nat.mul_le_mul_left _ hsc

end NearCubicWires.WireExponent3_5.PrimT.C4Bud
