import Proof.Wire_3_5.FinalPass.EnumCap3

/-! # The SYM enumeration's capacity, part 1: the exponent arithmetic under the load floor

P3:3011-3016 with the load `Ψ_S = C_D²(k+L)²(⌊√B_S⌋+L)` (P3:3094-3107). At a SYM call the group size bound is
below `2^E` (`EnumCap.qG_lt_pow`), `E` built from the entry exponent `e_N(k+L)`, the seed length `ℓ ≤ (e_Q+2)(k+L)`,
`k_h ≤ k`, `R ≤ 10`, `TWd = d_T L²` and the row-word exponent `(26L+7)D + k + 80L + 24`, with the degree bound
`D ≤ 384(f_e L + 1) + 1 + 3(71 + 12k + ZL)(23296⌊√B_S⌋ + 23553)` (`lbP_le` at `B' = 8192·B_S`). Then
`17 + 6E ≤ ⌊n/16⌋ + d_C L²` once `16·symC1 ≤ C_D` (a load floor fixed before `F`) and `symDC ≤ d_C`: the capacity
`Cap = 2^{⌊n/16⌋ + d_C β²}` of the free numbers covers `capC·(qG+1)^6`.

* `symC1`, `symDC`, **`symE_num`**.

Paper quantity of the main type: the SYM enumeration's size exponent against the capacity's exponent. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr

/-- The load floor's constant for the capacity (`16·symC1 ≤ C_D`). -/
def symC1 (eN eQ Z : ℕ) : ℕ := 6 * eN + 384 * eQ + 6215244 + 48114 * ((83 + Z) * 23553)

/-- The capacity exponent's constant (`symDC ≤ d_C`). -/
def symDC (dT fe : ℕ) : ℕ := 12 * dT + 6158592 * fe + 12839

/-- **The SYM size exponent below the capacity's exponent.** -/
theorem symE_num (K L S ell kh R Dg fe Z eN eQ dT dC CD psi n : ℕ)
    (hL : 1 ≤ L) (hell : ell ≤ (eQ + 2) * (K + L)) (hkh : kh ≤ K) (hR : R ≤ 10)
    (hDg : Dg ≤ 384 * (fe * L + 1) + 1 + 3 * ((71 + 12 * K + Z * L) * (23296 * S + 23553)))
    (hpsi : CD * CD * ((K + L) * (K + L) * (S + L)) ≤ psi) (hn : psi ≤ n)
    (hCD : 16 * symC1 eN eQ Z ≤ CD) (hdC : symDC dT fe ≤ dC) :
    17 + 6 * (eN * (K + L) + 2 * (14 + 24 * ell + 40 * kh + dT * (L * L) + 8 * ell + 8 * R) +
      (8 * R + 1) * ((26 * L + 7) * Dg + K + 80 * L + 24) + 5) ≤ n / 16 + dC * (L * L) := by
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU] at hpsi
  have hSL : 1 ≤ S + L := by omega
  have hV : 1 ≤ K + L := by omega
  have hVU : K + L ≤ U := by
    rw [hU]
    calc K + L = (K + L) * 1 * 1 := by ring
      _ ≤ (K + L) * (K + L) * (S + L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hV) hSL
  -- the list bound's product
  obtain ⟨W1, hW1⟩ : ∃ W, W = (71 + 12 * K + Z * L) * (23296 * S + 23553) := ⟨_, rfl⟩
  rw [← hW1] at hDg
  have w1 : 71 + 12 * K + Z * L ≤ (83 + Z) * (K + L) := by
    have e : (83 + Z) * (K + L) = 83 * K + 83 * L + Z * K + Z * L := by ring
    omega
  have w2 : 23296 * S + 23553 ≤ 23553 * (S + L) := by omega
  have w3 : L * W1 ≤ (83 + Z) * 23553 * U := by
    rw [hW1, hU]
    calc L * ((71 + 12 * K + Z * L) * (23296 * S + 23553))
        ≤ (K + L) * (((83 + Z) * (K + L)) * (23553 * (S + L))) :=
          Nat.mul_le_mul (by omega) (Nat.mul_le_mul w1 w2)
      _ = (83 + Z) * 23553 * ((K + L) * (K + L) * (S + L)) := by ring
  -- the degree bound times `L`
  have d1 : L * Dg ≤ 384 * (fe * (L * L)) + 385 * L + 3 * (L * W1) := by
    have := Nat.mul_le_mul_left L hDg
    have e : L * (384 * (fe * L + 1) + 1 + 3 * W1) = 384 * (fe * (L * L)) + 385 * L + 3 * (L * W1) := by ring
    omega
  have d2 : (26 * L + 7) * Dg ≤ 33 * (L * Dg) := by
    have := Nat.mul_le_mul_right Dg (show 26 * L + 7 ≤ 33 * L by omega)
    have e : 33 * L * Dg = 33 * (L * Dg) := by ring
    omega
  obtain ⟨eb, heb⟩ : ∃ e, e = (26 * L + 7) * Dg + K + 80 * L + 24 := ⟨_, rfl⟩
  rw [← heb]
  have d3 : (8 * R + 1) * eb ≤ 81 * eb := Nat.mul_le_mul_right _ (by omega)
  -- the seed length
  have hell' : ell ≤ eQ * (K + L) + 2 * (K + L) := by
    have e : (eQ + 2) * (K + L) = eQ * (K + L) + 2 * (K + L) := by ring
    omega
  -- the floor: `symC1·U ≤ n/16`
  have hC1 : 1 ≤ CD := by unfold symC1 at hCD; omega
  have f1 : 16 * symC1 eN eQ Z * U ≤ CD * CD * U :=
    Nat.mul_le_mul_right _ (le_trans hCD (Nat.le_mul_of_pos_left _ hC1))
  have f2 : symC1 eN eQ Z * U ≤ n / 16 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have e : 16 * symC1 eN eQ Z * U = symC1 eN eQ Z * U * 16 := by ring
    omega
  have f3 : symC1 eN eQ Z * U = 6 * (eN * U) + 384 * (eQ * U) + 6215244 * U + 48114 * ((83 + Z) * 23553 * U) := by
    unfold symC1; ring
  have t1 : eN * (K + L) ≤ eN * U := Nat.mul_le_mul_left _ hVU
  have t2 : eQ * (K + L) ≤ eQ * U := Nat.mul_le_mul_left _ hVU
  -- the capacity exponent
  have g1 : symDC dT fe * (L * L) ≤ dC * (L * L) := Nat.mul_le_mul_right _ hdC
  have g2 : symDC dT fe * (L * L) = 12 * (dT * (L * L)) + 6158592 * (fe * (L * L)) + 12839 * (L * L) := by
    unfold symDC; ring
  have hLL : 1 ≤ L * L := Nat.mul_pos hL hL
  omega

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
