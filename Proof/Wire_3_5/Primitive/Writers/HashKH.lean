import Proof.Wire_3_5.Primitive.Writers.HashClass

/-! # (HASH (d4)), part 3: the dimension's cubic coefficient `K_H`

The HASH dimension `m = k + L + K_H·L³` (`K_L = 0`) must exceed the aux filter's seed length plus one (the seeds'
count and the entries' count `nHash = 2^{seedBits}·2^k` fit `2^m`) and the exponent of the FILTER row's
`(len+2)^{D_f(e+1)}` (`FiltPipeLe2`). With `a ≤ α·L` (every THR number `≤ 2^a`), `e ≤ 10a² + 23a + 10 ≤ β·L²`, the
aux population `len + 2 ≤ 2^{26L+3}`, the aux cap `cap + 1 ≤ 2^{c_A + Z·L}` and `seedBits_le`, both are at most
`K_H·L³` with **`khOf α c_A Z D_f = 6000(30 + c_A + Z + β) + 1 + 29·D_f(β+1)`**.

* `betaOf`, `khOf`; **`kh_cond`**.

Paper quantities of the main type: the aux filter's seeds `2^{O(L²)}` and its evaluation cost `2^{O(D·L³)}`
(P3:2210-2211, 2220-2226) within the HASH dimension. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.HashSizes

/-- `β = 10α² + 23α + 10`. -/
def betaOf (α : ℕ) : ℕ := 10 * α * α + 23 * α + 10

/-- **The cubic coefficient** `K_H`. -/
def khOf (α cA Z Df : ℕ) : ℕ := 6000 * (30 + cA + Z + betaOf α) + 1 + 29 * Df * (betaOf α + 1)

theorem e_le_beta {a α e L : ℕ} (hL : 1 ≤ L) (ha : a ≤ α * L) (he : e ≤ 10 * a * a + 23 * a + 10) :
    e ≤ betaOf α * L ^ 2 := by
  unfold betaOf
  have h1 : a * a ≤ (α * L) * (α * L) := Nat.mul_le_mul ha ha
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h1L : 1 ≤ L ^ 2 := by nlinarith
  have e1 : (α * L) * (α * L) = α * α * L ^ 2 := by ring
  have h2 : α * L ≤ α * L ^ 2 := Nat.mul_le_mul_left _ hLL
  have e2 : (10 * α * α + 23 * α + 10) * L ^ 2 = 10 * (α * α * L ^ 2) + 23 * (α * L ^ 2) + 10 * L ^ 2 := by ring
  rw [e2]
  have e3 : 10 * a * a = 10 * (a * a) := by ring
  rw [e3] at he
  rw [e1] at h1
  omega

/-- **`K_H` works**: `seedBits + 1 + D_f(e+1)⌈log₂(len+2)⌉ ≤ K_H·L³`. -/
theorem kh_cond {L a α e len capA cA Z sb Df : ℕ} (hL : 1 ≤ L) (ha : a ≤ α * L)
    (he : e ≤ 10 * a * a + 23 * a + 10) (hlen : len + 2 ≤ 2 ^ (26 * L + 3)) (hcapA : capA + 1 ≤ 2 ^ (cA + Z * L))
    (hsb : sb ≤ 6000 * (Nat.clog 2 (len + 1) + Nat.clog 2 (capA + 1) + e + 1)) :
    sb + 1 + Df * (e + 1) * Nat.clog 2 (len + 2) ≤ khOf α cA Z Df * L ^ 3 := by
  have heb := e_le_beta hL ha he
  have c1 : Nat.clog 2 (len + 2) ≤ 26 * L + 3 := Nat.clog_le_of_le_pow hlen
  have c0 : Nat.clog 2 (len + 1) ≤ 26 * L + 3 := le_trans (Nat.clog_mono_right 2 (by omega)) c1
  have c2 : Nat.clog 2 (capA + 1) ≤ cA + Z * L := Nat.clog_le_of_le_pow hcapA
  have hLL : L ≤ L ^ 2 := by nlinarith
  have h1L : 1 ≤ L ^ 2 := by nlinarith
  have hL23 : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL (by norm_num)
  obtain ⟨β, hβ⟩ : ∃ b, b = betaOf α := ⟨_, rfl⟩
  rw [← hβ] at heb
  -- the seed length
  have s1 : sb ≤ 6000 * (30 + cA + Z + β) * L ^ 2 := by
    have z1 : Z * L ≤ Z * L ^ 2 := Nat.mul_le_mul_left _ hLL
    have z2 : 26 * L ≤ 26 * L ^ 2 := Nat.mul_le_mul_left _ hLL
    have z3 : cA ≤ cA * L ^ 2 := Nat.le_mul_of_pos_right _ h1L
    have e1 : 6000 * (30 + cA + Z + β) * L ^ 2 =
        6000 * (30 * L ^ 2 + cA * L ^ 2 + Z * L ^ 2 + β * L ^ 2) := by ring
    rw [e1]
    omega
  -- the FILTER row's exponent
  have f1 : Df * (e + 1) * Nat.clog 2 (len + 2) ≤ 29 * Df * (β + 1) * L ^ 3 := by
    have g1 : e + 1 ≤ (β + 1) * L ^ 2 := by
      have e1 : (β + 1) * L ^ 2 = β * L ^ 2 + L ^ 2 := by ring
      omega
    have g2 : Nat.clog 2 (len + 2) ≤ 29 * L := by omega
    calc Df * (e + 1) * Nat.clog 2 (len + 2) ≤ Df * ((β + 1) * L ^ 2) * (29 * L) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ g1) g2
      _ = 29 * Df * (β + 1) * (L ^ 2 * L) := by ring
      _ = 29 * Df * (β + 1) * L ^ 3 := by ring
  have s2 : 6000 * (30 + cA + Z + β) * L ^ 2 ≤ 6000 * (30 + cA + Z + β) * L ^ 3 :=
    Nat.mul_le_mul_left _ hL23
  have s3 : 1 ≤ L ^ 3 := le_trans h1L hL23
  have eK : khOf α cA Z Df * L ^ 3 =
      6000 * (30 + cA + Z + β) * L ^ 3 + L ^ 3 + 29 * Df * (β + 1) * L ^ 3 := by
    unfold khOf; rw [← hβ]; ring
  rw [eK]
  omega

end NearCubicWires.WireExponent3_5.PrimAsm.HashSizes
