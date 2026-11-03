import Proof.Wire_3_5.Primitive.SeedFix.C4SymNC
import Proof.Wire_3_5.Primitive.SeedFix.C4CapF

/-! # C4.K SYM item (b) v2: the SYM numbers machine at the unary capacity `2·2^{⌊n/8⌋ + C} + 2`

P3:2929-2941, 2994-3000, 3011-3016, 3098-3100 (the selection class `2^{q/2 + c_sel k}`), P3:3105-3115: `sym_bigS`
at the capacity v2: the M61 sizes `2^{O((B+1)²)}` fit `2^{⌊n/8⌋ + C}` through `C4Cap.mul_sq_le_div16`, and the
free numbers (contract v5: `K·2^{⌊n/8⌋}`) fit once `C ≥ ⌈log₂ K⌉ + 1`.

* `fitA`, `of_K`, `add8`, `mono8`, **`sym_fits2`**, **`sym_bigS2`**.

Paper quantities of the main type: the SYM stage's words at the call's `Q`, `ℓ`, `n_T`, `dRow`, and the capacity
`2^{⌊n/8⌋ + C}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.C4SymN
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.Filters NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.PrimT.C4Set

theorem fitA {X a m : ℕ} (h : X ≤ 2 ^ a) (hm : a + 1 ≤ m) : X + 1 ≤ 2 ^ m := by
  have h1 : 2 ^ a + 1 ≤ 2 ^ (a + 1) := by rw [pow_succ]; have := Nat.one_le_two_pow (n := a); omega
  exact le_trans (by omega) (le_trans h1 (Nat.pow_le_pow_right (by norm_num) hm))

theorem of_K {X K e : ℕ} (h : X ≤ K * 2 ^ e) : X ≤ 2 ^ (e + Nat.clog 2 K) := by
  rw [pow_add]
  calc X ≤ K * 2 ^ e := h
    _ ≤ 2 ^ Nat.clog 2 K * 2 ^ e := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by norm_num) K)
    _ = 2 ^ e * 2 ^ Nat.clog 2 K := Nat.mul_comm _ _

theorem add8 {X Y e a b : ℕ} (hX : X ≤ 2 ^ (e + a)) (hY : Y ≤ 2 ^ (e + b)) : X + Y ≤ 2 ^ (e + (a + b + 1)) := by
  have h1 : X ≤ 2 ^ (e + (a + b)) := le_trans hX (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h2 : Y ≤ 2 ^ (e + (a + b)) := le_trans hY (Nat.pow_le_pow_right (by norm_num) (by omega))
  have h3 : 2 ^ (e + (a + b + 1)) = 2 ^ (e + (a + b)) * 2 := by rw [← pow_succ]; ring_nf
  omega

theorem mono8 {X e a b : ℕ} (hab : a ≤ b) (h : X ≤ 2 ^ (e + a)) : X ≤ 2 ^ (e + b) :=
  le_trans h (Nat.pow_le_pow_right (by norm_num) (by omega))

end NearCubicWires.WireExponent3_5.PrimT.C4SymN
