import Proof.Wire_3_5.FinalPass.SymFr3Base

/-! # The SYM free numbers (root #145 (ii)), part 5: the exact recovery range `hrange`

"Suppose `0 ≤ V(z) ≤ J` on every column, choose `Q ≥ 1` with `2^Q > J`, and put `Q' = Q+m−1`" (alg:compiler,
P3:1886-1890) and "`V_p(z) ≤ 2^{8ℓ−|p|}·|T|·N^8(QN²)^8`" (samp:range, P3:2919-2921): the child's scaled value
`2^{m−1}·V_p(z)` is below `2^{Q'}` once `Q'` exceeds `m + 8ℓ + 24kh + log|T| + 8 log Q`.
* **`sampElim_lt`** (generic in the seed parameters and the state type);
* `cS`, **`hrange_sym`**: at a SYM call, `Q' = dQ(2kh+β)` with `dQ ≥ cS + 401` (`cS = 16eQ + eN + 40`).
Paper quantity of the main type: the exact recovery range of the child's printed objective. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.Sampler

/-- **The child's scaled value is below `2^{Q'}`** once `m + 8ℓ + 24kh + a + 8q < Q'` (`|T| ≤ 2^a`, `Q ≤ 2^q`). -/
theorem sampElim_lt (P : SeedParams) {T : Type} [Fintype T] (Dz : T → Cell P.N → Bool) (plen pre : ℕ)
    (hplen : plen ≤ 8 * P.ell) (m Qp a q : ℕ) (hT : Fintype.card T ≤ 2 ^ a) (hQ : P.Q ≤ 2 ^ q)
    (h : m + 8 * P.ell + 24 * P.kh + a + 8 * q < Qp) :
    (2 : ℤ) ^ (m - 1) * SeedFix.sampElim P Dz plen pre < 2 ^ Qp := by
  have hle := SeedFix.sampElim_le P Dz plen pre hplen
  have h0 := SeedFix.sampElim_nonneg P Dz plen pre hplen
  have hN : P.N = 2 ^ P.kh := rfl
  have hX : 2 ^ (8 * P.ell - plen) * (Fintype.card T * (P.N ^ 8 * (P.Q * P.N ^ 2) ^ 8)) ≤
      2 ^ (8 * P.ell + a + 24 * P.kh + 8 * q) := by
    rw [hN]
    have e : 2 ^ (8 * P.ell + a + 24 * P.kh + 8 * q) =
        2 ^ (8 * P.ell) * (2 ^ a * ((2 ^ P.kh) ^ 8 * (2 ^ q * (2 ^ P.kh) ^ 2) ^ 8)) := by
      ring
    rw [e]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le _ _))
      (Nat.mul_le_mul hT (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hQ) 8)))
  have hXz : SeedFix.sampElim P Dz plen pre ≤ ((2 ^ (8 * P.ell + a + 24 * P.kh + 8 * q) : ℕ) : ℤ) := by
    refine le_trans hle ?_
    exact_mod_cast hX
  have h2 : (2 : ℤ) ^ (m - 1) * ((2 ^ (8 * P.ell + a + 24 * P.kh + 8 * q) : ℕ) : ℤ) < 2 ^ Qp := by
    push_cast
    rw [← pow_add]
    exact pow_lt_pow_right₀ (by norm_num) (by omega)
  calc (2 : ℤ) ^ (m - 1) * SeedFix.sampElim P Dz plen pre
      ≤ (2 : ℤ) ^ (m - 1) * ((2 ^ (8 * P.ell + a + 24 * P.kh + 8 * q) : ℕ) : ℤ) :=
        mul_le_mul_of_nonneg_left hXz (by positivity)
    _ < 2 ^ Qp := h2

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr

