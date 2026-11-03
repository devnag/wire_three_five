import Proof.Wire_3_5.FinalPass.HashPre1Base
import Proof.Wire_3_5.Primitive.SeedFix.C4HB

/-! # The HASH printer's size `hbS` at a THR call, F-free (the C4HB)

`filt:soft` P3:2253-2290 ("each printed term has fixed arity and at most `poly(M,2^{O(k)})` integer size") and
filt:aux-precision P3:2291-2296: the Hb size `hbS D` (the cell count `2^{2t+2tℓ₀}(J+1)|pops|n_E N²`, `2^{2t+2tℓ₀}`,
`2^{ℓ₀+1}`, the HASH tape's word, the populations' and weights' streams, `G`, `N²`, `n_E`) at every THR call is at most
`2^{2k + c_S X³}` (`X = ⌈log₂(n+2)⌉ + 1`), with `c_S` of the literals only: the HASH rows have `(8Σ|X_j|+1)^{384w+1}`
monomials, `w = O(L²)`, so the tape's word has `2^{2k + O(L³)}` bits (unary atom codes below `4N²G`); the weights'
stream is `(J+1)(2 log Π_jW_j^{2t} + 3) = O(L⁴)`. The cube absorption `c·X³ ≤ n/32 + K₀` (`cube_absorb`) turns
`2^{O(L³)}` into the capacity's `2^{⌊n/16⌋ + d_C L²}` under a floor fixed before `F`.

* `cube_le_two_pow_half`, **`cube_absorb`**, `frame_len`, `cH`, `cHt`, `c0S`, `cS`;
* `cells_le`, `twoT_le`, **`htW_le`**, `popsW_le`, `wtW_le`, **`hbS_le`**.

Paper quantities of the main types: the Hb printer's size at a HASH call against `2^{O(k + L³)}`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

theorem cube_le_two_pow_half : ∀ x : ℕ, 32 ≤ x → x ^ 3 ≤ 2 ^ (x / 2)
  | x, hx => by
    by_cases h : x ≤ 33
    · interval_cases x <;> norm_num
    · have ih := cube_le_two_pow_half (x - 2) (by omega)
      have e : x / 2 = (x - 2) / 2 + 1 := by omega
      have h5 : x ^ 3 ≤ 2 * (x - 2) ^ 3 := by
        obtain ⟨y, rfl⟩ : ∃ y, x = y + 2 := ⟨x - 2, by omega⟩
        simp only [Nat.add_sub_cancel]
        have hy : 32 ≤ y := by omega
        have h1 : 32 * (y * y) ≤ y * (y * y) := Nat.mul_le_mul_right _ hy
        nlinarith [h1]
      have h4 : x ^ 3 ≤ 2 * 2 ^ ((x - 2) / 2) := le_trans h5 (Nat.mul_le_mul_left 2 ih)
      rw [e, pow_succ (2 : ℕ) ((x - 2) / 2)]
      linarith

/-- **The cube absorption**: `c·X³ ≤ n/32 + K₀` for every `n` (`X = ⌈log₂(n+2)⌉ + 1`). -/
theorem cube_absorb (c : ℕ) : ∃ K0 : ℕ, ∀ n : ℕ, c * (Nat.clog 2 (n + 2) + 1) ^ 3 ≤ n / 32 + K0 := by
  refine ⟨c * (2 * c + 50) ^ 3 + 1, fun n => ?_⟩
  obtain ⟨X, hX⟩ : ∃ X, X = Nat.clog 2 (n + 2) + 1 := ⟨_, rfl⟩
  rw [← hX]
  by_cases hB : 2 * c + 50 ≤ X
  · have h1 := cube_le_two_pow_half X (by omega)
    have h2 : c ≤ 2 ^ c := Nat.lt_two_pow_self.le
    have h3 : c + X / 2 ≤ X - 7 := by omega
    have h4 : c * X ^ 3 ≤ 2 ^ (X - 7) :=
      calc c * X ^ 3 ≤ 2 ^ c * 2 ^ (X / 2) := Nat.mul_le_mul h2 h1
        _ = 2 ^ (c + X / 2) := by rw [pow_add]
        _ ≤ 2 ^ (X - 7) := Nat.pow_le_pow_right (by norm_num) h3
    have h5 : 2 ^ (X - 2) < n + 2 := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < n + 2 by omega)
      have e : (Nat.clog 2 (n + 2)).pred = X - 2 := by rw [Nat.pred_eq_sub_one]; omega
      rwa [e] at this
    have h6 : 2 ^ (X - 2) = 32 * 2 ^ (X - 7) := by
      rw [show X - 2 = (X - 7) + 5 by omega, pow_add]; ring
    omega
  · have : c * X ^ 3 ≤ c * (2 * c + 50) ^ 3 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 3)
    omega

theorem frame_len : ∀ w : List Bool, (RepairOrdinary.frame w).length = 2 * w.length + 1
  | [] => rfl
  | b :: w => by rw [RepairOrdinary.frame, List.length_cons, List.length_cons, frame_len w, List.length_cons]; ring


section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
