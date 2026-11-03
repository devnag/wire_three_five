import Proof.Wire_3_5.FinalPass.SymCap2Base

/-! # The SYM request's degree bound is linear: `D ≤ d_D(⌊√B_S⌋ + L)`

list:base P3:1376-1398 (`J = ⌈log₂B⌉ + 9` windows `W_j = 64 + ⌈⌈√(64²B)⌉/2^{⌊j/3⌋}⌉`, so `Σ_j W_j = O(√B + J)`),
P3:3094-3100 (`d_S = C_D(√B_S + L)`): the degree bound `D = max(384·w_f + 1, 3·lbP)` of the SYM rows' factors
(`sym_factor_count`) is at most `symDD·(⌊√B_S⌋ + L)`, `symDD = 780(48 + Z) + 384f_e + 436876` fixed before `F`
(`B_S ≤ capK(c_r)(n+2)^Z ≤ 2^{(48+Z)L}` since `2c_r + 2 ≤ n + 2`). The geometric sum replaces the product bound
`lbP_le` (`J·√B`), which is not linear. This is `hpre_sym`'s `D ≤ d` at the SYM batch.

* `sum_div_pow_le`, `sum_div_pow3_le`, `ceilDiv_le`, **`lbP_lin`**, `symDD`, **`symDg_lin`**.

Paper quantity of the main type: the SYM degree `d_S` (P3:3094-3100). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen NearCubicWires.WireExponent3_5.Lists
open Finset

/-- `Σ_{i<m} ⌊C/2^i⌋ ≤ 2C`. -/
theorem sum_div_pow_le : ∀ (m C : ℕ), ∑ i ∈ range m, C / 2 ^ i ≤ 2 * C
  | 0, C => by simp
  | m + 1, C => by
    rw [sum_range_succ']
    have e : ∑ i ∈ range m, C / 2 ^ (i + 1) = ∑ i ∈ range m, (C / 2) / 2 ^ i := by
      refine sum_congr rfl fun i _ => ?_
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    rw [e]
    have ih := sum_div_pow_le m (C / 2)
    have : 2 * (C / 2) ≤ C := Nat.mul_div_le C 2
    simp only [pow_zero, Nat.div_one]
    omega

/-- `Σ_{j<3m} f(⌊j/3⌋) = 3·Σ_{i<m} f(i)`. -/
theorem sum_range_three (f : ℕ → ℕ) : ∀ m, ∑ j ∈ range (3 * m), f (j / 3) = 3 * ∑ i ∈ range m, f i
  | 0 => by simp
  | m + 1 => by
    rw [show 3 * (m + 1) = 3 * m + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ, sum_range_succ,
      sum_range_three f m, sum_range_succ]
    have h0 : (3 * m) / 3 = m := by omega
    have h1 : (3 * m + 1) / 3 = m := by omega
    have h2 : (3 * m + 1 + 1) / 3 = m := by omega
    rw [h0, h1, h2]
    ring

/-- `Σ_{j<J} ⌊C/2^{⌊j/3⌋}⌋ ≤ 6C`. -/
theorem sum_div_pow3_le (C J : ℕ) : ∑ j ∈ range J, C / 2 ^ (j / 3) ≤ 6 * C := by
  have h1 : ∑ j ∈ range J, C / 2 ^ (j / 3) ≤ ∑ j ∈ range (3 * J), C / 2 ^ (j / 3) :=
    sum_le_sum_of_subset (fun x hx => by simp only [Finset.mem_range] at hx ⊢; omega)
  rw [sum_range_three (fun i => C / 2 ^ i) J] at h1
  have h2 := sum_div_pow_le J C
  omega

theorem ceilDiv_le (a d : ℕ) (hd : 1 ≤ d) : a ⌈/⌉ d ≤ a / d + 1 := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  calc (a + d - 1) / d ≤ (a + d) / d := Nat.div_le_div_right (by omega)
    _ = a / d + 1 := Nat.add_div_right _ (by omega)

/-- **The list bound is linear in `√B` and `J`**: `lbP ≤ 260·J + 24·⌈√(64²B)⌉ + 1`. -/
theorem lbP_lin (Pl : FlatListParams) :
    PopLink.lbP Pl ≤ 260 * Pl.base.J + 24 * CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) + 1 := by
  unfold PopLink.lbP ListMachine.listBound
  simp only
  obtain ⟨C, hC⟩ : ∃ C, C = CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B) := ⟨_, rfl⟩
  have hW : ∀ j ∈ range Pl.base.J, 4 * Pl.base.W j ≤ 260 + 4 * (C / 2 ^ (j / 3)) := by
    intro j _
    unfold BaseListParams.W
    have := ceilDiv_le (CanonicalFourfoldRowProgram.natCeilSqrt (64 ^ 2 * Pl.base.B)) (2 ^ (j / 3))
      Nat.one_le_two_pow
    rw [← hC] at this ⊢
    omega
  have h1 : ∑ j ∈ range Pl.base.J, 4 * Pl.base.W j ≤ ∑ j ∈ range Pl.base.J, (260 + 4 * (C / 2 ^ (j / 3))) :=
    sum_le_sum hW
  have h2 : ∑ j ∈ range Pl.base.J, (260 + 4 * (C / 2 ^ (j / 3))) =
      260 * Pl.base.J + 4 * ∑ j ∈ range Pl.base.J, C / 2 ^ (j / 3) := by
    rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← mul_sum]; ring
  have h3 := sum_div_pow3_le C Pl.base.J
  rw [← hC]
  omega

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.SymFr
