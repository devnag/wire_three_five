import Proof.Wire_3_5.FinalPass.SymCost1

/-! # The SYM child's cost, part 3: the step bound below the pad (the arithmetic)

P3:3098-3100 (the pad `2^ρ`, `ρ ≥ n − k + d_A L`) against one child's steps (`coreCost_le`:
`210000(q+1)^3 + Y + T`). **`kch_pow`**: with `q = 2^{e_C + e_X}`, `𝒮' ≤ 2^{e_O}`, the fixed fields and the displayed
parameters `≤ 2^{e_F}`, `qG + 1 ≤ 2^{e_C}`, `2·dRow ≤ n − k + 1` and `dRow + p + 2 ≤ 2^{e_P'}`, the three terms are
below `2^{n − k + d_A L − 4}` once (1) `3(e_C + e_X) + 27`, (2) `8e_O + 32e_F + 8e_C + 94` are `≤ n − k + d_A L` and
(3) `C_w + 1034023 + ex·e_P' ≤ d_A L`. **`kch_exp`**: (1)-(3) at the SYM exponents under the load floor
`symHC ≤ C_D` and `symDAc ≤ d_A` (both fixed before `F`).

* `kch_pow`, `cUtOf`, `symHC`, `symDAc`, **`kch_exp`**.

Paper quantity of the main type: one child's steps against the pad `2^ρ`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr

/-- **The three terms of one child's steps below `2^{n − k + d_A L − 4}`.** -/
theorem kch_pow (eC eX eO eF ePr E1 dA L q O F Bn G dRow pr Cw ex : ℕ)
    (hq : q = 2 ^ eC * 2 ^ eX) (hO : O ≤ 2 ^ eO) (hF : F ≤ 2 ^ eF) (hB : Bn ≤ 2 ^ eF) (hG : G + 1 ≤ 2 ^ eC)
    (hdR : 2 * dRow ≤ E1 + 1) (hPr : dRow + pr + 2 ≤ 2 ^ ePr)
    (h1 : 3 * (eC + eX) + 27 ≤ E1 + dA * L) (h2 : 8 * eO + 32 * eF + 8 * eC + 94 ≤ E1 + dA * L)
    (h3 : Cw + 1034023 + ex * ePr ≤ dA * L) :
    210000 * (q + 1) ^ 3 + 52802 * (O * (256 * F ^ 3 + 2 * G + 1) * Bn) ^ 8 +
      (Cw + 1034014) * (2 ^ dRow + 1) ^ 2 * (dRow + pr + 2) ^ ex ≤ 2 ^ (E1 + dA * L - 4) := by
  obtain ⟨E, hE⟩ : ∃ E, E = E1 + dA * L := ⟨_, rfl⟩
  rw [← hE] at h1 h2 ⊢
  -- the first term
  have hq1 : q = 2 ^ (eC + eX) := by rw [hq, pow_add]
  have t1 : 210000 * (q + 1) ^ 3 ≤ 2 ^ (E - 6) := by
    have hq0 : 1 ≤ q := by rw [hq1]; exact Nat.one_le_two_pow
    have a1 : (q + 1) ^ 3 ≤ (2 * q) ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have a2 : (2 * q) ^ 3 = 8 * 2 ^ (3 * (eC + eX)) := by rw [hq1, mul_pow, ← pow_mul]; ring
    have a3 : (2 : ℕ) ^ (21 + 3 * (eC + eX)) ≤ 2 ^ (E - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a4 : (2 : ℕ) ^ (21 + 3 * (eC + eX)) = 2097152 * 2 ^ (3 * (eC + eX)) := by rw [pow_add]; norm_num
    generalize (2 : ℕ) ^ (3 * (eC + eX)) = W at a2 a4
    generalize (q + 1) ^ 3 = V at a1
    omega
  -- the second term
  have t2 : 52802 * (O * (256 * F ^ 3 + 2 * G + 1) * Bn) ^ 8 ≤ 2 ^ (E - 6) := by
    have a1 : F ^ 3 ≤ 2 ^ (3 * eF) := pow_mono_mul 3 hF
    have a2 : 256 * F ^ 3 + 2 * G + 1 ≤ 2 ^ (3 * eF + eC + 9) := by
      have b1 : 1 ≤ (2 : ℕ) ^ (3 * eF) := Nat.one_le_two_pow
      have b2 : 1 ≤ (2 : ℕ) ^ eC := Nat.one_le_two_pow
      have b3 : (2 : ℕ) ^ (3 * eF + eC + 9) = 512 * (2 ^ (3 * eF) * 2 ^ eC) := by rw [pow_add, pow_add]; ring
      have b4 : 2 ^ (3 * eF) ≤ 2 ^ (3 * eF) * 2 ^ eC := Nat.le_mul_of_pos_right _ b2
      have b5 : 2 ^ eC ≤ 2 ^ (3 * eF) * 2 ^ eC := Nat.le_mul_of_pos_left _ b1
      rw [b3]
      generalize (2 : ℕ) ^ (3 * eF) * 2 ^ eC = W at b4 b5
      generalize (2 : ℕ) ^ (3 * eF) = X at a1 b1 b4
      generalize (2 : ℕ) ^ eC = Y at hG b2 b5
      generalize F ^ 3 = Z at a1
      omega
    have a3 : O * (256 * F ^ 3 + 2 * G + 1) * Bn ≤ 2 ^ (eO + (3 * eF + eC + 9) + eF) := by
      rw [pow_add, pow_add]; exact Nat.mul_le_mul (Nat.mul_le_mul hO a2) hB
    have a4 := pow_mono_mul 8 a3
    have a5 : (2 : ℕ) ^ (16 + 8 * (eO + (3 * eF + eC + 9) + eF)) ≤ 2 ^ (E - 6) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have a6 : (2 : ℕ) ^ (16 + 8 * (eO + (3 * eF + eC + 9) + eF)) = 65536 * 2 ^ (8 * (eO + (3 * eF + eC + 9) + eF)) := by
      rw [pow_add]; norm_num
    generalize (2 : ℕ) ^ (8 * (eO + (3 * eF + eC + 9) + eF)) = W at a4 a6
    generalize (O * (256 * F ^ 3 + 2 * G + 1) * Bn) ^ 8 = V at a4
    omega
  -- the third term
  have t3 : (Cw + 1034014) * (2 ^ dRow + 1) ^ 2 * (dRow + pr + 2) ^ ex ≤ 2 ^ (E - 6) := by
    have a1 : Cw + 1034014 ≤ 2 ^ (Cw + 1034014) := lt_pow_self' _
    have a2 : (2 ^ dRow + 1) ^ 2 ≤ 2 ^ (E1 + 3) := by
      have b1 : 2 ^ dRow + 1 ≤ 2 ^ (dRow + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := dRow); omega
      calc (2 ^ dRow + 1) ^ 2 ≤ (2 ^ (dRow + 1)) ^ 2 := Nat.pow_le_pow_left b1 2
        _ = 2 ^ (2 * dRow + 2) := by rw [← pow_mul]; ring_nf
        _ ≤ 2 ^ (E1 + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have a3 : (dRow + pr + 2) ^ ex ≤ 2 ^ (ex * ePr) := pow_mono_mul ex hPr
    calc (Cw + 1034014) * (2 ^ dRow + 1) ^ 2 * (dRow + pr + 2) ^ ex
        ≤ 2 ^ (Cw + 1034014) * 2 ^ (E1 + 3) * 2 ^ (ex * ePr) := Nat.mul_le_mul (Nat.mul_le_mul a1 a2) a3
      _ = 2 ^ (Cw + 1034014 + (E1 + 3) + ex * ePr) := by rw [← pow_add, ← pow_add]
      _ ≤ 2 ^ (E - 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e4 : (2 : ℕ) ^ (E - 4) = 4 * 2 ^ (E - 6) := by
    rw [show E - 4 = (E - 6) + 2 by omega, pow_add]; ring
  rw [e4]
  omega

/-- The load floor's `U` coefficient for the child's steps. -/
def cUtOf (cD dQ dD cO eNc eQc : ℕ) : ℕ := 41 * (cD + dQ + dD + 400) + 11 * cO + 3 * (eNc + 8 * eQc + 24)

/-- **The child's-steps load floor** (`symHC ≤ C_D`, fixed before `F`). -/
def symHC (dC cD dQ dD cO eNc eQc : ℕ) : ℕ := 64 * dC + 8 * cUtOf cD dQ dD cO eNc eQc + 8

/-- **The pad's exponent constant** (`symDAc ≤ d_A`). -/
def symDAc (eH eP dH dP Cw ex : ℕ) : ℕ :=
  41 * (eH + eP + 26) + 41 * (dH + dP + 10) + 200 + Cw + 1034023 + ex * (dP + 2) + ex * (eP + 1)

/-- **The exponent conditions (1)-(3) at the SYM exponents**, under the floors. -/
theorem kch_exp (n K L S CD psi dC dA cD dQ dD dH eH dP eP cO eNc eQc Cw ex : ℕ) (hL : 1 ≤ L)
    (hpsiU : CD * CD * ((K + L) * (K + L) * (S + L)) ≤ psi) (hpsiL : CD * (L * L) ≤ psi)
    (hpsiK : CD * (K + L) ≤ psi) (hn : psi ≤ n)
    (hCD : symHC dC cD dQ dD cO eNc eQc ≤ CD) (hdA : symDAc eH eP dH dP Cw ex ≤ dA) :
    3 * ((n / 16 + dC * (L * L)) + (3 * efOf cD dQ dD dH eH dP eP ((K + L) * (K + L) * (S + L)) L +
        (eNc + 8 * eQc + 24 + cO) * ((K + L) * (K + L) * (S + L)) + 9)) + 27 ≤ (n - K) + dA * L ∧
      8 * (cO * ((K + L) * (K + L) * (S + L))) + 32 * efOf cD dQ dD dH eH dP eP ((K + L) * (K + L) * (S + L)) L +
        8 * (n / 16 + dC * (L * L)) + 94 ≤ (n - K) + dA * L ∧
      Cw + 1034023 + ex * (dP + 2 + (eP + 1) * L) ≤ dA * L := by
  obtain ⟨U, hU⟩ : ∃ U, U = (K + L) * (K + L) * (S + L) := ⟨_, rfl⟩
  rw [← hU] at hpsiU ⊢
  have hC1 : 1 ≤ CD := by unfold symHC at hCD; omega
  -- the floor facts
  have f1 : 64 * (dC * (L * L)) ≤ n := by
    have : 64 * dC ≤ CD := by unfold symHC at hCD; omega
    have := Nat.mul_le_mul_right (L * L) this
    have e : 64 * dC * (L * L) = 64 * (dC * (L * L)) := by ring
    omega
  have f2 : 8 * (cUtOf cD dQ dD cO eNc eQc * U) ≤ n := by
    have a : 8 * cUtOf cD dQ dD cO eNc eQc ≤ CD * CD := by
      have : CD ≤ CD * CD := Nat.le_mul_self _
      unfold symHC at hCD; omega
    have := Nat.mul_le_mul_right U a
    have e : 8 * cUtOf cD dQ dD cO eNc eQc * U = 8 * (cUtOf cD dQ dD cO eNc eQc * U) := by ring
    omega
  have f3 : 8 * K ≤ n := by
    have : 8 ≤ CD := by unfold symHC at hCD; omega
    have := Nat.mul_le_mul_right (K + L) this
    omega
  have eC : cUtOf cD dQ dD cO eNc eQc * U =
      41 * ((cD + dQ + dD + 400) * U) + 11 * (cO * U) + 3 * ((eNc + 8 * eQc + 24) * U) := by unfold cUtOf; ring
  have eF : efOf cD dQ dD dH eH dP eP U L = (cD + dQ + dD + 400) * U + (eH + eP + 26) * L + dH + dP + 10 := rfl
  have eX : (eNc + 8 * eQc + 24 + cO) * U = (eNc + 8 * eQc + 24) * U + cO * U := by ring
  -- the pad's exponent
  have g1 : symDAc eH eP dH dP Cw ex * L ≤ dA * L := Nat.mul_le_mul_right _ hdA
  have g2 : symDAc eH eP dH dP Cw ex * L = 41 * ((eH + eP + 26) * L) + (41 * (dH + dP + 10) + 200) * L +
      (Cw + 1034023) * L + ex * (dP + 2) * L + ex * ((eP + 1) * L) := by unfold symDAc; ring
  have g3 : 41 * (dH + dP + 10) + 200 ≤ (41 * (dH + dP + 10) + 200) * L := Nat.le_mul_of_pos_right _ hL
  have g4 : Cw + 1034023 ≤ (Cw + 1034023) * L := Nat.le_mul_of_pos_right _ hL
  have g5 : ex * (dP + 2) ≤ ex * (dP + 2) * L := Nat.le_mul_of_pos_right _ hL
  have g6 : ex * (dP + 2 + (eP + 1) * L) = ex * (dP + 2) + ex * ((eP + 1) * L) := by ring
  rw [eF, eX, g6]
  refine ⟨by omega, by omega, by omega⟩

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
