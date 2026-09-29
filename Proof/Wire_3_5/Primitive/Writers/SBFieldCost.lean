import Proof.Wire_3_5.Primitive.Writers.SBTypes2

/-! # SB: the field phase's cost target, proved

* `zerosCost_eq`, `eraseListCost_eq`, `eraseL_length`, `two_pow_ell` (`2^ℓ ≤ 32·len`), `fieldCost_le` (within
  `10^7·cap^4` once `4ℓ + 6 ≤ cap` and `len ≤ cap`), **`sbFieldCost : SBFieldCostStmt l`**.

Donors: `GF2.searchCost_le` (the primitive search, `2^{O(ℓ)}`), `PrimT.tauCost_le` (`250·(ℓ+1)^4`).

Paper quantity of the main type: SB's budget (`prim:runtime`, P3:3105-3115), the field words' cost (P3:2053-2055). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

theorem zerosCost_eq (cap ℓ : ℕ) : ∀ k : ℕ, SBFieldA.zerosCost cap ℓ k = k * (UnaryPow.sq cap + 29 * ℓ + 18)
  | 0 => by simp [SBFieldA.zerosCost]
  | k + 1 => by
    show UnaryPow.sq cap + 1 + (29 * ℓ + 16) + 1 + SBFieldA.zerosCost cap ℓ k = (k + 1) * (UnaryPow.sq cap + 29 * ℓ + 18)
    rw [zerosCost_eq cap ℓ k]; ring

theorem eraseListCost_eq (cap T : ℕ) : ∀ L : List ℕ, SBWords.eraseListCost cap T L = L.length * (UnaryPow.sq cap + 16 * T + 5)
  | [] => by simp [SBWords.eraseListCost]
  | _ :: L => by
    show UnaryPow.sq cap + 1 + (16 * T + 3 + 1 + SBWords.eraseListCost cap T L) = (L.length + 1) * (UnaryPow.sq cap + 16 * T + 5)
    rw [eraseListCost_eq cap T L]; ring

theorem eraseL_length : ((SBField.eraseL FsB).map fun i => i.val).length = 21 := by
  simp [SBField.eraseL]; decide

theorem two_pow_nbl_le (x : ℕ) : 2 ^ natBitLength x ≤ 2 * (x + 1) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · rw [pow_succ]; have := Nat.pow_log_le_self 2 (show x ≠ 0 by omega); omega

theorem two_pow_ell (n : ℕ) : 2 ^ ellOf n ≤ 32 * ((n + 1) ^ 26 * 2) := by
  unfold ellOf
  have h1 : 1 ≤ (n + 1) ^ 26 := Nat.one_le_pow _ _ (by omega)
  generalize (n + 1) ^ 26 = Y at h1 ⊢
  have h := two_pow_nbl_le (Y * 2 - 1)
  have e : Y * 2 - 1 + 1 = Y * 2 := by omega
  rw [e] at h
  rw [pow_add]
  calc 2 ^ natBitLength (Y * 2 - 1) * 2 ^ 4 ≤ 2 * (Y * 2) * 2 ^ 4 := Nat.mul_le_mul_right _ h
    _ = 32 * (Y * 2) := by ring

/-- **The field phase within `10^7·cap^4`.** -/
theorem fieldCost_le (n cap : ℕ) (hl : 4 * ellOf n + 6 ≤ cap) (hlen : (n + 1) ^ 26 * 2 ≤ cap) :
    SBField.fieldCost cap (ellOf n) ((SBField.eraseL FsB).map fun i => i.val) ≤ 10 ^ 7 * cap ^ 4 := by
  have h1 : 1 ≤ cap := by omega
  have hc2 : cap ^ 2 ≤ cap ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have hc3 : cap ^ 3 ≤ cap ^ 4 := Nat.pow_le_pow_right h1 (by norm_num)
  have hc1 : cap ≤ cap ^ 4 := by have := Nat.pow_le_pow_right h1 (show 1 ≤ 4 by norm_num); rwa [pow_one] at this
  have hsq : UnaryPow.sq cap ≤ 1800 * cap ^ 4 := by
    unfold UnaryPow.sq
    have : (cap + 2) * (cap + 2) ≤ 9 * cap ^ 2 := by nlinarith
    nlinarith
  -- the search
  have hℓ1 : 1 ≤ ellOf n := by unfold ellOf; omega
  have hs := GF2.searchCost_le (ellOf n) (ellOf n) hℓ1 le_rfl
  have hp : 2 ^ ellOf n ≤ 32 * cap := (two_pow_ell n).trans (Nat.mul_le_mul_left 32 hlen)
  have hp2 : 2 ^ (2 * ellOf n) ≤ (32 * cap) * (32 * cap) := by
    rw [pow_mul', sq]; exact Nat.mul_le_mul hp hp
  have hs2 : GF2.searchCost (ellOf n) ≤ 204800 * cap ^ 4 := by
    have e1 : 2 ^ (2 * ellOf n) * ellOf n ^ 1 ≤ ((32 * cap) * (32 * cap)) * cap := by
      rw [pow_one]; exact Nat.mul_le_mul hp2 (by omega)
    have e2 : ((32 * cap) * (32 * cap)) * cap = 1024 * cap ^ 3 := by ring
    rw [e2] at e1
    have := hs.trans (Nat.mul_le_mul_left 200 e1)
    have e3 : 200 * (1024 * cap ^ 3) = 204800 * cap ^ 3 := by ring
    rw [e3] at this
    exact this.trans (Nat.mul_le_mul_left _ hc3)
  -- the trace mask
  have ht := PrimT.tauCost_le (ellOf n)
  have ht2 : PrimT.tauCost (ellOf n) ≤ 4000 * cap ^ 4 := by
    have e1 : (ellOf n + 1) ^ 4 ≤ (2 * cap) ^ 4 := Nat.pow_le_pow_left (by omega) 4
    have e2 : (2 * cap) ^ 4 = 16 * cap ^ 4 := by ring
    rw [e2] at e1
    omega
  unfold SBField.fieldCost SBField.w3Cost Modulus.modCost
  rw [zerosCost_eq, eraseListCost_eq, eraseL_length]
  generalize UnaryPow.sq cap = Q at hsq ⊢
  generalize GF2.searchCost (ellOf n) = G at hs2 ⊢
  generalize PrimT.tauCost (ellOf n) = T at ht2 ⊢
  generalize ellOf n = L at hl hℓ1 ⊢
  generalize cap ^ 4 = X at hc1 hsq hs2 ht2 ⊢
  clear * - hsq hs2 ht2 hl hc1
  omega

/-- **The field phase's cost target, proved.** -/
theorem sbFieldCost (l : Literals) : SBFieldCostStmt l := by
  refine ⟨10 ^ 7, 4, fun F P m wl c0 c1 nc cap h => ?_⟩
  have hp := need_parts l F.cr F.filterErrDeg P m wl c0 c1 nc cap h
  have ht1 := hp.1
  have hl := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlen : (P.n + 1) ^ 26 * 2 ≤ cap := by
    refine le_trans ?_ ht1
    unfold tB1
    omega
  exact fieldCost_le P.n cap hl hlen

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
