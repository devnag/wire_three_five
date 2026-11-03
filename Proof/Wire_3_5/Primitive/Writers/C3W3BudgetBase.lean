import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase

/-! # PA2: the C3 writers' budget at the polynomial load premise

`C3Cost.call_budget` (M47) with the premise `h + Q' + m + pr ≤ c_N·(Ψ+1)·(n+1)^{D_N}`. The size's polynomial part is
raised to `(n+1)^{D₀+D_N}` (`omega_factsD`, `size_leD`, the size bound at any degree `D`), so the class is
`EW3 l D_N = 2^{(D₀+D_N+2)·d_G·Ψ}` (**`call_budget3`**); `k + L ≤ Ψ` (the load floor `C_D ≥ 1`) absorbs `(n+1)^{D_N}`.

Paper quantity of the main type: the writers' steps within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108,
3170-3173). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.SupplierPipeline NearCubicWires.LocalBitMultitape NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.PrimAsm.C3Mach NearCubicWires.WireExponent3_5.PrimAsm.C3Field
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.CompilerMachine.Pool

variable (l : Literals) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The size bound at degree `D`**: `(S₀+1)^d ≤ (K+1)^d·2^{(D+2)·d·Ψ}` once `S₀ ≤ K·2^k(n+1)^{D}(Ψ+1)` and
`k + L ≤ Ψ`. -/
theorem size_leD (n k psi L K S0 d D : ℕ) (hk : k + L ≤ psi) (hL : n + 2 ≤ 2 ^ L)
    (hS : S0 ≤ K * (2 ^ k * (n + 1) ^ D * (psi + 1))) :
    (S0 + 1) ^ d ≤ (K + 1) ^ d * 2 ^ ((D + 2) * d * psi) := by
  have h1 : 2 ^ k ≤ 2 ^ psi := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : n + 1 ≤ 2 ^ psi := le_trans (by omega) (le_trans hL (Nat.pow_le_pow_right (by norm_num) (by omega)))
  have h3 : (n + 1) ^ D ≤ (2 ^ psi) ^ D := Nat.pow_le_pow_left h2 _
  have h4 : psi + 1 ≤ 2 ^ psi := Nat.lt_two_pow_self
  have hΩ : 2 ^ k * (n + 1) ^ D * (psi + 1) ≤ 2 ^ ((D + 2) * psi) := by
    calc 2 ^ k * (n + 1) ^ D * (psi + 1) ≤ 2 ^ psi * (2 ^ psi) ^ D * 2 ^ psi := by gcongr
      _ = 2 ^ ((D + 2) * psi) := by rw [← pow_mul, ← pow_add, ← pow_add]; ring_nf
  have h5 : S0 + 1 ≤ (K + 1) * 2 ^ ((D + 2) * psi) := by
    calc S0 + 1 ≤ K * (2 ^ k * (n + 1) ^ D * (psi + 1)) + 2 ^ k * (n + 1) ^ D * (psi + 1) := by
          have : 0 < 2 ^ k * (n + 1) ^ D * (psi + 1) := by positivity
          omega
      _ = (K + 1) * (2 ^ k * (n + 1) ^ D * (psi + 1)) := by ring
      _ ≤ (K + 1) * 2 ^ ((D + 2) * psi) := Nat.mul_le_mul_left _ hΩ
  calc (S0 + 1) ^ d ≤ ((K + 1) * 2 ^ ((D + 2) * psi)) ^ d := Nat.pow_le_pow_left h5 _
    _ = (K + 1) ^ d * 2 ^ ((D + 2) * d * psi) := by rw [mul_pow, ← pow_mul]; ring_nf

theorem omega_factsD (n k psi DN : ℕ) :
    1 ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) ∧ n ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) ∧
      psi + 1 ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) ∧
      (∀ e, e ≤ D0 → (n + 1) ^ e ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1)) ∧
      (∀ e, e ≤ D0 → 2 ^ k * (n + 1) ^ e ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1)) ∧
      (psi + 1) * (n + 1) ^ DN ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by
  have hk : 1 ≤ 2 ^ k := Nat.one_le_two_pow
  have hD : 1 ≤ D0 := by unfold D0; omega
  have hn : n + 1 ≤ (n + 1) ^ (D0 + DN) := Nat.le_self_pow (by omega) _
  have hp : 1 ≤ (n + 1) ^ (D0 + DN) := Nat.one_le_pow _ _ (by omega)
  have b1 : (n + 1) ^ (D0 + DN) ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by
    calc (n + 1) ^ (D0 + DN) = 1 * (n + 1) ^ (D0 + DN) * 1 := by ring
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by gcongr <;> omega
  have b2 : psi + 1 ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by
    calc psi + 1 = 1 * 1 * (psi + 1) := by ring
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by gcongr
  refine ⟨by omega, by omega, b2, fun e he => le_trans (Nat.pow_le_pow_right (by omega) (by omega)) b1,
    fun e he => ?_, ?_⟩
  · calc 2 ^ k * (n + 1) ^ e ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * 1 := by
          rw [mul_one]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := Nat.mul_le_mul_left _ (by omega)
  · calc (psi + 1) * (n + 1) ^ DN ≤ (psi + 1) * (n + 1) ^ (D0 + DN) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
      _ = 1 * (n + 1) ^ (D0 + DN) * (psi + 1) := by ring
      _ ≤ 2 ^ k * (n + 1) ^ (D0 + DN) * (psi + 1) := by gcongr

end NearCubicWires.WireExponent3_5.PrimAsm.C3Cost
