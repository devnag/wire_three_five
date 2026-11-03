import Proof.Wire_3_5.UnionMachine.ThrUnitRunBase
import Proof.Wire_3_5.UnionMachine.ThrUnitIface5Base
import Proof.Wire_3_5.Primitive.Writers.ThrBud2Base
import Proof.Wire_3_5.FinalPass.ThrSz3
import Proof.Wire_3_5.Primitive.Writers.CallSizeBase

/-! # The THR unit's measure absorbed by the THR load `Ψ_T` (THRU4's `meas_le`), part 1: the RADIX measure

At a THR call, with `L = ⌈log₂(n+2)⌉` and `Y = L²`, every number of the RADIX row's measure `radMeas5` (P3:2585-2623)
is `2^{O(L²)}` uniformly in the gate (PA's THR side bounds: `occ_le`, `thrPool_le`, `dig_le2`, `thrCallJ_le`,
`thrCallT_le`, `Bs_le2`, `hbC_le`; `thr_ell_le`'s `k_h ≤ bsq n`; `ThrSz.levelWord_le`, `majW_le`, `payOf_le`;
`CallSize.wordBound_poly`), except the digit lists' counting capacity `(8G+2)^{3·lb+1}`, `lb = listBound(thrCallD)`,
which is `2^{(3·lb+1)(26L+7)}`:

* the atoms: `lw_le` (the table word), `word_le` (the request and the hash bits), `pw_le` (`(M+1)^{2τ₀}`),
  `digsN_le` (the digit program's measure), `mlab_le`, `row_le`;
* **`radMeas5_le`**: `radMeas5 … pr row ≤ 2^{(3·lb+1)(26L+7) + K_R·L² + 8}` at every prime and star row;
* `KR l` (the constant, from `l` only).

Paper quantity: the RADIX row's explicit capacity, within `2^{O(Ψ_T)}` (P3:3094-3108) once `lb·L ≤ c·Ψ_T`
(`ThrUnit.lb_absorbT`). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.RepairOrdinary (frame)
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (pow_N_le one_le_L n2_le_L pow_mono_mul)

/-! ## Arithmetic -/

theorem nbl_le_L (n : ℕ) : natBitLength n ≤ Nat.clog 2 (n + 2) := by
  unfold natBitLength
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.log_zero_right, zero_add]; exact one_le_L 0
  · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) (show n < 2 ^ Nat.clog 2 (n + 2) from
      lt_of_lt_of_le (by omega) (n2_le_L n))
    omega

theorem le_two_pow_self (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

theorem two_pow_mono {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

theorem mul_le_two_pow (c x : ℕ) : c * x ≤ 2 ^ (c * x) := le_two_pow_self _

/-- The word bound's polynomial constants. -/
noncomputable def cW : ℕ := Classical.choose CallSize.wordBound_poly
noncomputable def dW : ℕ := Classical.choose (Classical.choose_spec CallSize.wordBound_poly)

theorem wordBound_le (n : ℕ) : CallSize.wordBound 26 26 2 n ≤ cW * (n + 1) ^ dW :=
  (Classical.choose_spec (Classical.choose_spec CallSize.wordBound_poly)).2 n

/-- The row: at most `N² ≤ 2^{8L²}`. -/
theorem sq_le (kh L : ℕ) (hkh : kh ≤ (L + 1) ^ 2) (hL : 1 ≤ L) : (2 ^ kh) ^ 2 ≤ 2 ^ (8 * (L * L)) := by
  rw [← pow_mul]
  apply two_pow_mono
  have e : (L + 1) ^ 2 = L * L + 2 * L + 1 := by ring
  have : L ≤ L * L := Nat.le_mul_of_pos_left L hL
  omega

/-- **The digit lists' counting capacity and the numbers**: `radX` below `2^{(3lb+1)(26L+7) + E + 4}`. -/
theorem radX_le (M τ G Mlab lb lw p L E : ℕ) (hG8 : 8 * G + 2 ≤ 2 ^ (26 * L + 7)) (hM : M ≤ 2 ^ E) (hτ : τ ≤ 2 ^ E)
    (hG : G ≤ 2 ^ E) (hMl : Mlab ≤ 2 ^ E) (hlw : lw ≤ 2 ^ E) (hp : p ≤ 2 ^ E) :
    RadSpec.radX M τ G Mlab lb lw p 2 ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E + 4) := by
  unfold RadSpec.radX
  have h1 := pow_mono_mul (3 * lb + 1) hG8
  have h2 : lb ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7)) := by
    have := le_two_pow_self lb
    exact this.trans (two_pow_mono (by nlinarith))
  have a1 : 2 ^ ((3 * lb + 1) * (26 * L + 7)) ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := two_pow_mono (by omega)
  have a2 : 2 ^ E ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := two_pow_mono (by omega)
  have a3 : 2 ^ ((3 * lb + 1) * (26 * L + 7) + E + 4) = 16 * 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := by
    rw [pow_add]; ring
  have a4 : 1 ≤ 2 ^ ((3 * lb + 1) * (26 * L + 7) + E) := Nat.one_le_two_pow
  omega

section Call

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
