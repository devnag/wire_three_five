import Proof.Wire_3_5.Primitive.SeedFix.C4CapA
import Proof.Wire_3_5.Primitive.SeedFix.C4SJ

/-! # C4 cap re-type, part 4: the capacity's bounds (mode-generic)

P3:2929-2941, 2994-3000 (the numbers `ℓ`, `Q`, `n_T·2^w` the numbers machine holds) and P3:3098-3100 (the selection
class `2^{q/2 + c_sel k}q^{A_sel}` covers the capacity's cost `2^{O(B²)}`, `B` the bit length of `q`, through its
`q/2`): for any mode,
* **`le_capB`**: a value `X ≤ K·2^{D(B+1)²}` fits the capacity `2^{capExp C n}` once `C ≥ D + ⌈log₂K⌉ + 1`
  (`X + 1 ≤ 2^{capExp C n}`; every numbers-machine cap `X + X + 3 ≤ 2·2^m + 2`, `Q + 1`, `2Q`, … follows);
* `sq_le_two_pow_half`, `mul_sq_le_two_pow`, **`capExp_le_half`**: `C·(B+1)² ≤ n/2 + K₀` for every `n` (the
  capacity's cost in the selection class's `2^{n/2}`, the finitely many small `n` in the coefficient `c₄`).

Paper quantity of the main types: the capacity exponent `capExp C n` against the call's values and the class bound. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Cap
open NearCubicWires

/-- `x² ≤ 2^{x/2}` from `x = 18`. -/
theorem sq_le_two_pow_half : ∀ x : ℕ, 18 ≤ x → x ^ 2 ≤ 2 ^ (x / 2)
  | x, hx => by
    by_cases h : x ≤ 19
    · interval_cases x <;> norm_num
    · have ih := sq_le_two_pow_half (x - 2) (by omega)
      have e : x / 2 = (x - 2) / 2 + 1 := by omega
      have h5 : x ^ 2 ≤ 2 * (x - 2) ^ 2 := by
        obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
        simp only [Nat.add_sub_cancel]
        nlinarith
      have h4 : x ^ 2 ≤ 2 * 2 ^ ((x - 2) / 2) := le_trans h5 (Nat.mul_le_mul_left 2 ih)
      rw [e, pow_succ (2 : ℕ) ((x - 2) / 2)]
      linarith

/-- `c·(B+1)² ≤ 2^{B−2}` from `B = 4c + 20`. -/
theorem mul_sq_le_two_pow (c B : ℕ) (hB : 4 * c + 20 ≤ B) : c * (B + 1) ^ 2 ≤ 2 ^ (B - 2) := by
  have h1 := sq_le_two_pow_half (B + 1) (by omega)
  have h2 : c ≤ 2 ^ c := (Nat.lt_two_pow_self).le
  have h3 : c + (B + 1) / 2 ≤ B - 2 := by omega
  calc c * (B + 1) ^ 2 ≤ 2 ^ c * 2 ^ ((B + 1) / 2) := Nat.mul_le_mul h2 h1
    _ = 2 ^ (c + (B + 1) / 2) := by rw [pow_add]
    _ ≤ 2 ^ (B - 2) := Nat.pow_le_pow_right (by norm_num) h3

/-- **The capacity exponent is below `n/2` up to a constant**: `c·(B+1)² ≤ n/2 + K₀` for every `n`. -/
theorem capExp_le_half (c : ℕ) : ∃ K0 : ℕ, ∀ n : ℕ, c * (natBitLength n + 1) ^ 2 ≤ n / 2 + K0 := by
  refine ⟨c * (4 * c + 21) ^ 2 + 1, fun n => ?_⟩
  obtain ⟨B, hBd⟩ : ∃ B, B = natBitLength n := ⟨_, rfl⟩
  rw [← hBd]
  by_cases hB : 4 * c + 20 ≤ B
  · have h1 := mul_sq_le_two_pow c B hB
    have hn : n ≠ 0 := by
      intro h0; rw [h0] at hBd; unfold natBitLength at hBd; simp at hBd; omega
    have h2 : 2 ^ (B - 1) ≤ n := by
      rw [hBd]; unfold natBitLength; simp only [Nat.add_sub_cancel]
      exact Nat.pow_log_le_self 2 hn
    have h3 : 2 ^ (B - 2) * 2 = 2 ^ (B - 1) := by
      rw [← pow_succ]; congr 1; omega
    omega
  · have : c * (B + 1) ^ 2 ≤ c * (4 * c + 21) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)
    omega

end NearCubicWires.WireExponent3_5.PrimT.C4Cap
