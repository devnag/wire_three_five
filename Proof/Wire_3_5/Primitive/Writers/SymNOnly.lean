import Proof.Wire_3_5.Primitive.Writers.SymCosts
import Proof.Wire_3_5.Primitive.Writers.CallIndexR

/-! # SYM leaf, part 5: the length-only quantities of a SYM call, as `2^{aL+b}`

The SYM decode and the SYM dimension stage need capacities above quantities of the length `n` alone: the sparse
count's bound `SparseNum.sparseBound` at the schedule `t = rowBt n` (`t = O(log L)`, `Schedule.sched_log`), the mass
bound `Λ̄ = O(L^{3/16})` (`Ledger.rowBLambda_pow16_le`), the POP term `T`. Each is at most `2^{a·L + b}`
(`L = ⌈log₂(n+2)⌉`), `a` fixed with the floors, `b` after `F`:

* `sparse_le_P` (`≤ 20(L³+1)·X^{32(m+1)}`, `X = 2z_B + c₁ + c₂ + C_δ + 4`), **`sparse_le`**;
* `lambda_le`, `rowBt_le`, `two_pow_le` (`2^{aL+b} ≤ 2^{b+2a}(n+1)^a`), `self_le_two_pow`.

Paper quantities of the main types: the sparse count `s(q)` and the mass bound `Λ̄(q)` of the row-B ledger
(P3:3400, 3690-3691, 3820-3821). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimAsm.SparseNum

/-- `n ≤ 2^n`. -/
theorem self_le_two_pow (x : ℕ) : x ≤ 2 ^ x := (Nat.lt_two_pow_self).le

/-- `2^{aL+b} ≤ 2^{b+2a}·(n+1)^a` at `L = ⌈log₂(n+2)⌉`. -/
theorem two_pow_le (a b n : ℕ) : 2 ^ (a * Nat.clog 2 (n + 2) + b) ≤ 2 ^ (b + 2 * a) * (n + 1) ^ a := by
  have h1 : 2 ^ Nat.clog 2 (n + 2) ≤ 4 * (n + 1) := by
    have := PrimAsm.CallIndexR.two_pow_clog_le_two_mul (n + 2) (by omega)
    omega
  calc 2 ^ (a * Nat.clog 2 (n + 2) + b) = 2 ^ b * (2 ^ Nat.clog 2 (n + 2)) ^ a := by
        rw [pow_add, ← pow_mul, mul_comm a]; ring
    _ ≤ 2 ^ b * (4 * (n + 1)) ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 a)
    _ = 2 ^ (b + 2 * a) * (n + 1) ^ a := by rw [mul_pow, pow_add, pow_mul]; norm_num; ring

section Sparse
variable (ζ : ℚ) (Cδ : ℕ)

/-- The sparse bound's base `X`. -/
def spX : ℕ := 2 * zB ζ + c1 ζ + c2 ζ + Cδ + 4

theorem sparse_le_P (L m : ℕ) :
    sparseBound ζ Cδ L m ≤ 20 * (L ^ 3 + 1) * spX ζ Cδ ^ (32 * (m + 1)) := by
  obtain ⟨X, hX⟩ : ∃ x, x = spX ζ Cδ := ⟨_, rfl⟩
  rw [← hX]
  have hX4 : 4 ≤ X := by rw [hX]; unfold spX; omega
  have hX1 : 1 ≤ X := by omega
  have hz : zB ζ ≤ X := by rw [hX]; unfold spX; omega
  have hz2 : 2 * zB ζ ≤ X := by rw [hX]; unfold spX; omega
  have hc1 : c1 ζ ≤ X := by rw [hX]; unfold spX; omega
  have hc2 : c2 ζ ≤ X := by rw [hX]; unfold spX; omega
  have hd : Cδ ≤ X := by rw [hX]; unfold spX; omega
  obtain ⟨P, hP⟩ : ∃ p, p = X ^ (32 * (m + 1)) := ⟨_, rfl⟩
  have hp : ∀ e, e ≤ 32 * (m + 1) → X ^ e ≤ P := fun e he => by rw [hP]; exact Nat.pow_le_pow_right hX1 he
  have hP1 : 1 ≤ P := by rw [hP]; exact Nat.one_le_pow _ _ hX1
  have hXP : X ≤ P := by have := hp 1 (by omega); rwa [pow_one] at this
  -- the pieces
  have q1 : c2 ζ ^ 16 * (c1 ζ ^ 16) ^ m ≤ P := by
    calc c2 ζ ^ 16 * (c1 ζ ^ 16) ^ m ≤ X ^ 16 * (X ^ 16) ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hc2 _) (Nat.pow_le_pow_left (Nat.pow_le_pow_left hc1 _) _)
      _ = X ^ (16 + 16 * m) := by rw [← pow_mul, ← pow_add]
      _ ≤ P := hp _ (by omega)
  have q2 : (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ m ≤ P := by
    calc (2 * zB ζ) ^ 16 * (zB ζ ^ 16) ^ m ≤ X ^ 16 * (X ^ 16) ^ m :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hz2 _) (Nat.pow_le_pow_left (Nat.pow_le_pow_left hz _) _)
      _ = X ^ (16 + 16 * m) := by rw [← pow_mul, ← pow_add]
      _ ≤ P := hp _ (by omega)
  have hw : zB ζ * zB ζ ^ m * 4 ≤ X ^ (m + 2) := by
    calc zB ζ * zB ζ ^ m * 4 ≤ X * X ^ m * X :=
          Nat.mul_le_mul (Nat.mul_le_mul hz (Nat.pow_le_pow_left hz _)) (by omega)
      _ = X ^ (m + 2) := by ring
  have q3 : zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) * Cδ ≤ P := by
    calc zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) * Cδ ≤ X ^ (m + 2) * X ^ (m + 2) * X :=
          Nat.mul_le_mul (Nat.mul_le_mul hw hw) hd
      _ = X ^ (2 * m + 5) := by ring
      _ ≤ P := hp _ (by omega)
  have q4 : zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) ≤ P := by
    calc zB ζ * zB ζ ^ m * 4 * (zB ζ * zB ζ ^ m * 4) ≤ X ^ (m + 2) * X ^ (m + 2) := Nat.mul_le_mul hw hw
      _ = X ^ (2 * m + 4) := by ring
      _ ≤ P := hp _ (by omega)
  have q5 : zB ζ * zB ζ ^ m * 4 ≤ P := le_trans hw (hp _ (by omega))
  have q6 : c1 ζ ^ m * c2 ζ ≤ P := by
    calc c1 ζ ^ m * c2 ζ ≤ X ^ m * X := Nat.mul_le_mul (Nat.pow_le_pow_left hc1 _) hc2
      _ = X ^ (m + 1) := by ring
      _ ≤ P := hp _ (by omega)
  have q7 : c1 ζ ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hc1 _) (hp _ (by omega))
  have q8 : zB ζ ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hz _) (hp _ (by omega))
  have q9 : c2 ζ ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hc2 _) (hp _ (by omega))
  have q10 : (2 * zB ζ) ^ 16 ≤ P := le_trans (Nat.pow_le_pow_left hz2 _) (hp _ (by omega))
  have q11 : c1 ζ ^ m ≤ P := le_trans (Nat.pow_le_pow_left hc1 _) (hp _ (by omega))
  have q12 : m ≤ P := by
    have a1 : m < 2 ^ m := Nat.lt_two_pow_self
    have a2 : 2 ^ m ≤ X ^ m := Nat.pow_le_pow_left (by omega) _
    have a3 := hp m (by omega)
    omega
  have q13 : 8 ≤ P := by
    have a1 : 4 ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hX4 2
    have a2 := hp 2 (by omega)
    norm_num at a1; omega
  have hL : L ≤ L ^ 3 := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp
    · calc L = L ^ 1 := (pow_one L).symm
        _ ≤ L ^ 3 := Nat.pow_le_pow_right h (by norm_num)
  have r1 : L ^ 3 * c2 ζ ^ 16 * (c1 ζ ^ 16) ^ m ≤ L ^ 3 * P := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ q1
  have r2 : L ^ 3 ≤ L ^ 3 * P := Nat.le_mul_of_pos_right _ hP1
  have e : 20 * (L ^ 3 + 1) * P = 20 * (L ^ 3 * P) + 20 * P := by ring
  unfold sparseBound
  rw [← hP, e]
  omega

end Sparse

end NearCubicWires.WireExponent3_5.PrimAsm.SymSizes
