import Proof.Wire_3_5.UnionMachine.ThrUnitMeas2Base

/-! # The THR unit's measure absorbed by `Ψ_T`, part 3: the call's measure `measC ≤ c·2^{K_q·Ψ_T}`

At a THR call of a gate with `C_D ≥ 1` (`L = ⌈log₂(n+2)⌉`, `Ψ_T = loadThr C_D k L B_T`, P3:3094-3100):
`L⁴ ≤ Ψ_T` (`psi_L4`); the RADIX measures `2^{(3lb+1)(26L+7) + K_R L² + 8} ≤ 2^{K_1·Ψ_T}` through `lb·L ≤ c_Ab·Ψ_T`
(`ThrUnit.lb_absorbT`, `expo_rad`); the FILTER setup's arguments `2^{K_F L²}` and its pipeline's bound
`K_f·(f+2)^{D_f(f_e L+2)} ≤ K_f·2^{D_f(f_e+2)(K_F+1)Ψ_T}` (`expo_filt`); the decode front's need and bound
(quasi-polynomial, `2^{K·L²}`); the data counts. Hence **`measC_le`**: `measC ≤ c·2^{K_q·Ψ_T}` with the coefficient
`c = C_n + C_b + 16K_t + 32 + K_f + 3` (after the gate) and the exponent `K_q` from `l`, `f_e`, the decode front's
exponent bound `D₀`, `D_f` and `D_t` (before the gate).

Paper quantity: the THR unit's per-call measure within the preprocessing class `2^{O(Ψ_T)}` (P3:3089-3108). -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (pow_N_le one_le_L n2_le_L pow_mono_mul)

/-- `L⁴ ≤ Ψ_T` at `C_D ≥ 1`. -/
theorem psi_L4 (CD k L BT : ℕ) (hCD : 1 ≤ CD) : L * L * (L * L) ≤ loadThr CD k L BT := by
  refine le_trans ?_ (ThrUnit.loadThr_le' CD k L BT)
  have h1 : L * L ≤ (k + L) * (k + L) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : L * L ≤ Nat.sqrt (BT * L) + L * L := by omega
  have h3 : L * L * (L * L) ≤ (k + L) * (k + L) * (Nat.sqrt (BT * L) + L * L) := Nat.mul_le_mul h1 h2
  have h4 : 1 ≤ CD * CD := Nat.one_le_iff_ne_zero.mpr (by positivity)
  exact h3.trans (Nat.le_mul_of_pos_left _ h4)

/-- The RADIX exponent in `Ψ_T`. -/
theorem expo_rad (lb L Ψ cAb KRc : ℕ) (hL : 1 ≤ L) (h4 : L * L * (L * L) ≤ Ψ) (hlb : lb * L ≤ cAb * Ψ) :
    (3 * lb + 1) * (26 * L + 7) + KRc * (L * L) + 8 ≤ (99 * cAb + KRc + 41) * Ψ := by
  have hLL : 1 ≤ L * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hY : L * L ≤ Ψ := le_trans (Nat.le_mul_of_pos_right _ hLL) h4
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL
  have hlb1 : lb ≤ lb * L := Nat.le_mul_of_pos_right _ hL
  have hK : KRc * (L * L) ≤ KRc * Ψ := Nat.mul_le_mul_left _ hY
  have e1 : (3 * lb + 1) * (26 * L + 7) = 78 * (lb * L) + 21 * lb + 26 * L + 7 := by ring
  have e2 : (99 * cAb + KRc + 41) * Ψ = 99 * (cAb * Ψ) + KRc * Ψ + 41 * Ψ := by ring
  omega

/-- The FILTER pipeline's exponent in `Ψ_T`. -/
theorem expo_filt (fe L Ψ KFc Df : ℕ) (hL : 1 ≤ L) (h4 : L * L * (L * L) ≤ Ψ) :
    Df * (fe * L + 2) * (KFc * (L * L) + 2) ≤ Df * (fe + 2) * (KFc + 2) * Ψ := by
  have hLL : 1 ≤ L * L := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hLY : L ≤ L * L := Nat.le_mul_of_pos_left L hL
  have a1 : fe * L + 2 ≤ (fe + 2) * L := by nlinarith
  have a2 : KFc * (L * L) + 2 ≤ (KFc + 2) * (L * L) := by nlinarith
  have a3 : L * (L * L) ≤ L * L * (L * L) := by nlinarith
  calc Df * (fe * L + 2) * (KFc * (L * L) + 2) ≤ Df * ((fe + 2) * L) * ((KFc + 2) * (L * L)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) a2
    _ = Df * (fe + 2) * (KFc + 2) * (L * (L * L)) := by ring
    _ ≤ Df * (fe + 2) * (KFc + 2) * Ψ := Nat.mul_le_mul_left _ (a3.trans h4)

theorem two_pow_le_of {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) h

section Call

end Call

end NearCubicWires.WireExponent3_5.UnionMachine.ThrMeas
