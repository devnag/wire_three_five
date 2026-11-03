import Proof.Wire_3_5.UnionMachine.FrontSemTopSBase

/-! # C6 front, the time (0): the fixed-degree bookkeeping (`c6np`)

With `n ≥ 1` and every atom of a cost expression at most `n`, an expression built from `+`, `*`, `^k`, truncated `-`,
`/`, `max` and numerals is at most `C·n^D` with `C` and `D` read off the expression (**`c6np`**: `np_add`, `np_mul`,
`np_pow`, `np_sub`, `np_div`, `np_max`, `np_atom`, `np_const`); `np_fin` compares the result with a stated bound.

Paper quantity: none (bookkeeping for the front's time). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit

section NP
variable {n : ℕ}

theorem np_add (hn : 1 ≤ n) {a b A B i j : ℕ} (ha : a ≤ A * n ^ i) (hb : b ≤ B * n ^ j) :
    a + b ≤ (A + B) * n ^ (max i j) := by
  have h1 : n ^ i ≤ n ^ (max i j) := Nat.pow_le_pow_right hn (le_max_left _ _)
  have h2 : n ^ j ≤ n ^ (max i j) := Nat.pow_le_pow_right hn (le_max_right _ _)
  have h3 : A * n ^ i ≤ A * n ^ (max i j) := Nat.mul_le_mul_left _ h1
  have h4 : B * n ^ j ≤ B * n ^ (max i j) := Nat.mul_le_mul_left _ h2
  rw [Nat.add_mul]; omega

theorem np_mul {a b A B i j : ℕ} (ha : a ≤ A * n ^ i) (hb : b ≤ B * n ^ j) : a * b ≤ (A * B) * n ^ (i + j) := by
  calc a * b ≤ (A * n ^ i) * (B * n ^ j) := Nat.mul_le_mul ha hb
    _ = (A * B) * n ^ (i + j) := by rw [pow_add]; ring

theorem np_pow {a A i : ℕ} (ha : a ≤ A * n ^ i) (k : ℕ) : a ^ k ≤ A ^ k * n ^ (i * k) := by
  calc a ^ k ≤ (A * n ^ i) ^ k := Nat.pow_le_pow_left ha k
    _ = A ^ k * n ^ (i * k) := by rw [mul_pow, ← pow_mul]

theorem np_sub {a A i : ℕ} (ha : a ≤ A * n ^ i) (b : ℕ) : a - b ≤ A * n ^ i := (Nat.sub_le _ _).trans ha

theorem np_div {a A i : ℕ} (ha : a ≤ A * n ^ i) (b : ℕ) : a / b ≤ A * n ^ i := (Nat.div_le_self _ _).trans ha

theorem np_max (hn : 1 ≤ n) {a b A B i j : ℕ} (ha : a ≤ A * n ^ i) (hb : b ≤ B * n ^ j) :
    max a b ≤ (A + B) * n ^ (max i j) := (max_le_add_of_nonneg (Nat.zero_le _) (Nat.zero_le _)).trans (np_add hn ha hb)

theorem np_atom {x : ℕ} (h : x ≤ n) : x ≤ 1 * n ^ 1 := by rw [one_mul, pow_one]; exact h

theorem np_const (k : ℕ) : k ≤ k * n ^ 0 := by rw [pow_zero, mul_one]

theorem np_fin (hn : 1 ≤ n) {x A i C D : ℕ} (h : x ≤ A * n ^ i) (hC : A ≤ C) (hD : i ≤ D) : x ≤ C * n ^ D :=
  h.trans (Nat.mul_le_mul hC (Nat.pow_le_pow_right hn hD))

end NP

/-- Decompose a cost expression into atoms bounded by `n` (hypotheses `x ≤ n` in context) and numerals; needs
`hn : 1 ≤ n` in context. -/
syntax "c6np" : tactic
macro_rules
  | `(tactic| c6np) => `(tactic| first
      | with_reducible assumption
      | with_reducible exact np_atom (by assumption)
      | with_reducible exact le_trans (by assumption) (by c6np)
      | with_reducible exact np_add (by assumption) (by c6np) (by c6np)
      | with_reducible exact np_pow (by c6np) _
      | with_reducible exact np_mul (by c6np) (by c6np)
      | with_reducible exact np_sub (by c6np) _
      | with_reducible exact np_div (by c6np) _
      | with_reducible exact np_max (by assumption) (by c6np) (by c6np)
      | with_reducible exact np_const _)

/-- Close `x ≤ C·n^D` by `c6np` and numeral comparisons. -/
syntax "c6npf" : tactic
macro_rules
  | `(tactic| c6npf) => `(tactic| exact np_fin (by assumption) (by c6np) (by norm_num) (by norm_num))

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit
