import Statement_Wire_3_5
import StatementChecks.Theorem2_5_Nontrivial

/-! # Statement checks for row B

Realizes the checks of `thm:tradeoff` at row B (P3:225-238, P3:261-262) and the row-B parameter arithmetic
(P3:958-961, P3:3848-3852).
* SC1 (teeth): a constant language violates the row-B hardness. The zero-bottom symmetric circuit has `W = 0` and
  agreement `1`, and `1 ≥ 1/2 + L(n)^{-1/8}` once `L(n) ≥ 256`.
* SC3: `rowB` is the instance `WireExponent3_5 (1/8) (11/2) (9/2)`.
* The ledger arithmetic: with `τ = 3/16`, `K_{T,alg} = 87/16`, `K_{S,alg} = 71/16`, the load exponents
  `(K_0 + 2τ − K_alg)/2` are `−1/32`, the cap reserves are `1/16`, and `c < τ`, `K_T > 5 + 2c`, `K_S > 4 + 2c`.

Main types name the paper quantities `WireExponent3_5Hard (1/8) (11/2) (9/2)` (the agreement bound `1/2 + L(n)^{-1/8}`)
and the rational exponents of the row-B ledger. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.StatementChecks
open NearCubicWires NearCubicWires.WireExponent3_5

/-- SC3: the row-B instance of `thm:tradeoff` (P3:261-262). -/
theorem rowB_eq_instance : rowB = WireExponent3_5 (1 / 8) (11 / 2) (9 / 2) := rfl

/-- The row-B parameter arithmetic (P3:958-961, P3:3848-3852). -/
theorem rowB_ledger_arithmetic :
    ((5 : ℚ) + 2 * (3 / 16) - 87 / 16) / 2 = -1 / 32 ∧
    ((4 : ℚ) + 2 * (3 / 16) - 71 / 16) / 2 = -1 / 32 ∧
    (11 / 2 : ℚ) - 87 / 16 = 1 / 16 ∧ (9 / 2 : ℚ) - 71 / 16 = 1 / 16 ∧
    (1 / 8 : ℚ) < 3 / 16 ∧ (5 : ℚ) + 2 * (1 / 8) < 11 / 2 ∧ (4 : ℚ) + 2 * (1 / 8) < 9 / 2 := by
  norm_num

/-- `L ≥ 256` makes the row-B advantage `L^{-1/8}` at most one half. -/
theorem advantage_le_half {L : ℝ} (hL : 256 ≤ L) : L ^ (-((1 : ℝ) / 8)) ≤ 1 / 2 := by
  have hpos : (0 : ℝ) < L := by linarith
  have h256 : (256 : ℝ) ^ ((1 : ℝ) / 8) = 2 := by
    rw [show (256 : ℝ) = 2 ^ (8 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hmono : (256 : ℝ) ^ ((1 : ℝ) / 8) ≤ L ^ ((1 : ℝ) / 8) :=
    Real.rpow_le_rpow (by norm_num) hL (by norm_num)
  rw [h256] at hmono
  rw [Real.rpow_neg hpos.le]
  calc (L ^ ((1 : ℝ) / 8))⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hmono
    _ = 1 / 2 := by norm_num

/-- SC1, teeth: no constant language satisfies the row-B hardness. -/
theorem constant_language_fails (value : Bool) :
    ¬ WireExponent3_5Hard (1 / 8) (11 / 2) (9 / 2) (fun _ _ => value) := by
  intro h
  obtain ⟨onset, hon⟩ := h 1 1 one_pos one_pos
  set n := max onset (2 ^ 256) with hn
  have hsym := (hon n (le_max_left _ _)).2
    (Theorem2_5_Nontrivial.constantCircuit n value) (by
      simp only [Theorem2_5_Nontrivial.constantCircuit, Finset.univ_eq_empty, Finset.sum_empty,
        Nat.cast_zero]
      positivity)
  have hclog : 256 ≤ Nat.clog 2 (n + 2) := by
    by_contra hlt
    have hle : n + 2 ≤ 2 ^ 255 :=
      (Nat.clog_le_iff_le_pow (by norm_num)).1 (by omega)
    have : 2 ^ 256 ≤ n := le_max_right _ _
    have : (2 : ℕ) ^ 255 < 2 ^ 256 := Nat.pow_lt_pow_right (by norm_num) (by norm_num)
    omega
  have hL : (256 : ℝ) ≤ (Nat.clog 2 (n + 2) : ℝ) := by exact_mod_cast hclog
  have hadv := advantage_le_half hL
  have hone : ((Finset.univ.filter fun x : Fin n → Bool =>
      (Theorem2_5_Nontrivial.constantCircuit n value).eval x = value).card : ℝ) /
        (Fintype.card (Fin n → Bool) : ℝ) = 1 := by
    have hall : (Finset.univ.filter fun x : Fin n → Bool =>
        (Theorem2_5_Nontrivial.constantCircuit n value).eval x = value) = Finset.univ := by
      ext x
      simp [Theorem2_5_Nontrivial.constantCircuit_eval]
    rw [hall, Finset.card_univ]
    exact div_self (by positivity)
  rw [hone] at hsym
  linarith

end NearCubicWires.WireExponent3_5.StatementChecks
