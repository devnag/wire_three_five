import Proof.Wire_3_5.Primitive.Writers.ThrSide3

/-! # c4 THR block, piece 6 part 4: the THR size exponent below the capacity's (twin of the SymCap1)

P3:3011-3016 with the THR load `Ψ_T = C_D²(k+L)²(⌊√(B_T L)⌋ + L²)` (P3:3094-3107): the group size bound of the THR
enumeration is below `2^E` (`EnumCap.qG_lt_pow`), `E` built from `e_N(k+L)`, `ℓ ≤ (e_Q+2)(k+L)`, `k_h ≤ k`,
`R ≤ 3`, `TWd = d_T L²` and the THR row-word exponent `e_b` (the digits `≤ c_d L`, the degree `D ≤ d_D(√(B_T L) + L²)`);
then `17 + 6E ≤ ⌊n/16⌋ + d_C L²` once `16·thrC1 ≤ C_D` (a load floor fixed before `F`) and `12 d_T ≤ d_C`.

* `cbT`, `thrC1`, **`thrE_num`**.

Paper quantity of the main type: the THR enumeration's size exponent against the capacity's exponent. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide

/-- The row-word exponent's coefficient. -/
def cbT (cd dD : ℕ) : ℕ := 61 * cd + 66 * dD + 50

/-- **The THR load floor's constant** (`16·thrC1 ≤ C_D`). -/
def thrC1 (eN eQ cd dD : ℕ) : ℕ := 17 + 6 * (eN + 64 * eQ + 289 + 25 * cbT cd dD)

/-- **The THR size exponent below the capacity's exponent.** -/
theorem thrE_num (K L S ell kh R D dig eN eQ dT dC CD psi n cd dD : ℕ)
    (hL : 1 ≤ L) (hell : ell ≤ (eQ + 2) * (K + L)) (hkh : kh ≤ K) (hR : R ≤ 3)
    (hdig : dig ≤ cd * L) (hD : D ≤ dD * (S + L * L))
    (hpsi : CD * CD * ((K + L) * (K + L) * (S + L * L)) ≤ psi) (hn : psi ≤ n)
    (hCD : 16 * thrC1 eN eQ cd dD ≤ CD) (hdC : 12 * dT ≤ dC) :
    17 + 6 * (eN * (K + L) + 2 * (14 + 24 * ell + 40 * kh + dT * (L * L) + 8 * ell + 8 * R) +
      (8 * R + 1) * eb dig L D K + 5) ≤ n / 16 + dC * (L * L) := by
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L * L) := ⟨_, rfl⟩
  rw [← hU] at hpsi
  have hLL : 1 ≤ L * L := Nat.mul_pos hL hL
  have hSL : 1 ≤ S + L * L := by omega
  have hV : 1 ≤ K + L := by omega
  have hVV : L * L ≤ (K + L) * (K + L) := Nat.mul_le_mul (by omega) (by omega)
  have u1 : K + L ≤ U := by
    rw [hU]
    calc K + L = (K + L) * 1 * 1 := by ring
      _ ≤ (K + L) * (K + L) * (S + L * L) := Nat.mul_le_mul (Nat.mul_le_mul_left _ hV) hSL
  have u2 : L * L ≤ U := by
    rw [hU]
    calc L * L = L * L * 1 := by ring
      _ ≤ (K + L) * (K + L) * (S + L * L) := Nat.mul_le_mul hVV hSL
  have u3 : L * S + L * (L * L) ≤ U := by
    rw [hU]
    have h1 : L ≤ (K + L) * (K + L) := le_trans (Nat.le_mul_of_pos_right _ hL) hVV
    calc L * S + L * (L * L) = L * (S + L * L) := by ring
      _ ≤ (K + L) * (K + L) * (S + L * L) := Nat.mul_le_mul_right _ h1
  -- the row-word exponent `e_b ≤ cbT·U`
  have b1 : 2 * dig * (26 * L + 3) ≤ 58 * cd * U := by
    have h1 : 2 * dig * (26 * L + 3) ≤ 2 * (cd * L) * (29 * L) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hdig) (by omega)
    have h2 : 2 * (cd * L) * (29 * L) = 58 * cd * (L * L) := by ring
    have h3 : 58 * cd * (L * L) ≤ 58 * cd * U := Nat.mul_le_mul_left _ u2
    omega
  have b2 : 2 * dig + 1 ≤ (2 * cd + 1) * U := by
    have h1 : cd * L ≤ cd * U := Nat.mul_le_mul_left _ (le_trans (Nat.le_mul_of_pos_right _ hL) u2)
    have e : (2 * cd + 1) * U = 2 * (cd * U) + U := by ring
    have hU1 : 1 ≤ U := le_trans hLL u2
    omega
  have b3 : (26 * L + 6) * D + D ≤ 66 * dD * U := by
    have h1 : (26 * L + 6) * D + D ≤ 33 * L * D := by
      have e : 33 * L * D = 26 * L * D + 7 * L * D := by ring
      have h2 : 7 * D ≤ 7 * L * D := by
        have := Nat.mul_le_mul_right D (show 7 ≤ 7 * L by omega); omega
      have e2 : (26 * L + 6) * D = 26 * L * D + 6 * D := by ring
      omega
    have h2 : 33 * L * D ≤ 33 * L * (dD * (S + L * L)) := Nat.mul_le_mul_left _ hD
    have e3 : 33 * L * (dD * (S + L * L)) = 33 * dD * (L * S + L * (L * L)) := by ring
    have h4 : 33 * dD * (L * S + L * (L * L)) ≤ 33 * dD * U := Nat.mul_le_mul_left _ u3
    have e4 : 66 * dD * U = 2 * (33 * dD * U) := by ring
    omega
  have b4 : K + 26 * L + 6 + 4 ≤ 36 * U := by
    have hU1 : 1 ≤ U := le_trans hLL u2
    omega
  have hEb : eb dig L D K ≤ cbT cd dD * U := by
    unfold eb cbT
    have e : (61 * cd + 66 * dD + 50) * U = 58 * cd * U + (2 * cd + 1) * U + 66 * dD * U + 36 * U + (cd * U + 13 * U) := by
      ring
    rw [e]
    omega
  have hR8 : (8 * R + 1) * eb dig L D K ≤ 25 * (cbT cd dD * U) :=
    Nat.mul_le_mul (by omega) hEb
  -- the seed-block terms
  have hx1 : ell ≤ (eQ + 2) * U := le_trans hell (Nat.mul_le_mul_left _ u1)
  have hx2 : kh ≤ U := le_trans hkh (le_trans (Nat.le_add_right K L) u1)
  have hNU : eN * (K + L) ≤ eN * U := Nat.mul_le_mul_left _ u1
  have hU1 : 1 ≤ U := le_trans hLL u2
  -- the floor: `thrC1·U ≤ n/16`
  have hC1 : 1 ≤ CD := by unfold thrC1 at hCD; omega
  have f1 : 16 * thrC1 eN eQ cd dD * U ≤ CD * CD * U :=
    Nat.mul_le_mul_right _ (le_trans hCD (Nat.le_mul_of_pos_left _ hC1))
  have f2 : thrC1 eN eQ cd dD * U ≤ n / 16 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    have e : 16 * thrC1 eN eQ cd dD * U = thrC1 eN eQ cd dD * U * 16 := by ring
    omega
  have f3 : thrC1 eN eQ cd dD * U = 17 * U + 6 * (eN * U) + 384 * (eQ * U) + 1734 * U + 150 * (cbT cd dD * U) := by
    unfold thrC1; ring
  have g1 : 12 * dT * (L * L) ≤ dC * (L * L) := Nat.mul_le_mul_right _ hdC
  have e5 : (eQ + 2) * U = eQ * U + 2 * U := by ring
  have e6 : 12 * dT * (L * L) = 12 * (dT * (L * L)) := by ring
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
