import Proof.Wire_3_5.Filters.GF2Refs

/-! # S2-math: bit vectors as `𝔽₂` polynomials (the representation of `𝔽_{2^ℓ}`, P3:2932-2941)

Realizes the representation behind "Take `ℓ ≥ max{k, ⌈log₂(Q+1)⌉}` and a field `𝔽_{2^ℓ}` [...] A defining irreducible
polynomial and the arithmetic can be found and implemented in `2^{O(ℓ)}` elementary preprocessing time" (P3:2932-2941):
a natural number `a` is the polynomial `Σ_i a_i X^i ∈ 𝔽₂[X]` of its bits, so exclusive-or is addition, a left shift by
`i` is multiplication by `X^i`, and `a < 2^ℓ` is `deg < ℓ`. These are the facts the shift/XOR/masked-parity machine
refs of `Proof.Wire_3_5.Filters.GF2Refs` (the S2 machine targets) are read through.

(Seed fold v3: `toPoly`, `bitF`, `coeff_toPoly`, `toPoly_xor`, `toPoly_two_pow(_mul)`, `degree_toPoly_lt`,
`ModulusOk`, `natDegree_toPoly`, `toPoly_monic` and the bit lemmas now live in the seed module `Proof.Wire_3_5.Foundations.GF`;
this module keeps the rest.) Main declarations: **`toPoly`** (bits to polynomial) with **`coeff_toPoly`**, `toPoly_injective`, **`toPoly_xor`**
(`⊕ = +`), `toPoly_two_pow` (`2^b ↦ X^b`), **`toPoly_two_pow_mul`**/`toPoly_shiftLeft` (shift = multiply by `X^i`),
`toPoly_mod_two_pow_succ` (the low bits, one at a time), **`degree_toPoly_lt`** (`a < 2^ℓ ⟹ deg < ℓ`), and the modulus
facts **`toPoly_monic`**/**`natDegree_toPoly`** (bit `ℓ` set and `p < 2^{ℓ+1}`); the bit lemmas `lt_of_testBit_false`
and `lt_two_pow_of_testBit_eq`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.GF
open Polynomial

theorem toPoly_shiftLeft (a i : ℕ) : toPoly (a <<< i) = X ^ i * toPoly a := by
  rw [Nat.shiftLeft_eq, mul_comm, toPoly_two_pow_mul]

/-- Adding the next low bit. -/
theorem toPoly_mod_two_pow_succ (a j : ℕ) :
    toPoly (a % 2 ^ (j + 1)) = toPoly (a % 2 ^ j) + if a.testBit j then X ^ j else 0 := by
  ext i
  rw [coeff_add, coeff_toPoly, coeff_toPoly, Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
  rcases lt_trichotomy i j with h | rfl | h
  · have h1 : i < j + 1 := by omega
    have h2 : i ≠ j := by omega
    split_ifs <;> simp [h, h1, h2, coeff_X_pow]
  · split_ifs with hb <;> simp [hb, bitF]
  · have h1 : ¬ i < j + 1 := by omega
    have h2 : ¬ i < j := by omega
    have h3 : i ≠ j := by omega
    split_ifs <;> simp [h1, h2, h3, coeff_X_pow, bitF]

end NearCubicWires.WireExponent3_5.GF
