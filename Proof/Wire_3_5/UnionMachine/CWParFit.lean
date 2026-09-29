import Proof.Wire_3_5.UnionMachine.CWParSize

/-! # C6 front, U5, the code writers: the parity writer's loop fits its capacity

The bottoms' loop of the parity writer (P3:3092-3094) runs at the capacity `T = 10^25·(n+1)^24` computed from `1^n`
(`n = q`, the bitmap's length), and at the uniform round fuel `3·10^12·(9n+9)^12` (`CWParSize.round_le`):
* **`loop_fit`**: the fuel fits the capacity, and every round tape stays within it.
And a toolkit for polynomial bounds in powers of `Y ≥ 9` (constants absorbed into powers).

Paper quantity: none (the writer's time, a fixed polynomial). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParFit
open NearCubicWires NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParRound
open NearCubicWires.WireExponent3_5.UnionMachine.CWParPre (WLv SBv P3v)
open NearCubicWires.WireExponent3_5.UnionMachine.CWParSize
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- The loop's capacity coefficient. -/
def CP : ℕ := 10000000000000000000000000

/-- The loop's uniform round fuel. -/
def cwP (n : ℕ) : ℕ := 3000000000000 * (9 * n + 9) ^ 12

theorem nine_pow (n : ℕ) : (9 * n + 9) ^ 12 = 282429536481 * (n + 1) ^ 12 := by ring

/-- **The loop fits its capacity.** -/
theorem loop_fit (l : List Bool) :
    (∀ j < l.count true, roundPCost (WLv l) (P3v l) j (accOf (WLv l) (P3v l) j) ≤ cwP l.length) ∧
      cwP l.length + 1 ≤ BlockPlatform.UnaryCalc.value 24 CP l.length ∧
      (∀ j ≤ l.count true, ∀ t, (Qp (WLv l) (P3v l) j t).length ≤ BlockPlatform.UnaryCalc.value 24 CP l.length) := by
  set n := l.length with hn
  have hk : l.count true ≤ n := List.count_le_length
  have h12 : (n + 1) ^ 12 ≤ (n + 1) ^ 24 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h1 : 1 ≤ (n + 1) ^ 12 := Nat.one_le_pow _ _ (by omega)
  have hT : BlockPlatform.UnaryCalc.value 24 CP n = CP * (n + 1) ^ 24 := rfl
  have hcw : cwP n + 1 ≤ CP * (n + 1) ^ 24 := by
    unfold cwP CP; rw [nine_pow]; omega
  refine ⟨fun j hj => round_le l j (by omega), by rw [hT]; exact hcw, ?_⟩
  intro j hj t
  have w := widths l
  rw [← hn] at w
  have hP : (9 * n + 9) ^ 5 ≤ (9 * n + 9) ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hacc := acc_le l j (by omega)
  rw [← hn] at hacc
  have hacc2 : ((accOf (WLv l) (P3v l) j).flatMap frame).length ≤ 600 * (9 * n + 9) ^ 12 + 401 * n := by
    have e : j * (600 * (9 * n + 9) ^ 5 + 401) = 600 * (j * (9 * n + 9) ^ 5) + 401 * j := by ring
    have h6 : j * (9 * n + 9) ^ 5 ≤ (9 * n + 9) ^ 12 := by
      have a1 : j * (9 * n + 9) ^ 5 ≤ (9 * n + 9) * (9 * n + 9) ^ 5 := Nat.mul_le_mul_right _ (by omega)
      have a2 : (9 * n + 9) * (9 * n + 9) ^ 5 = (9 * n + 9) ^ 6 := by ring
      have a3 : (9 * n + 9) ^ 6 ≤ (9 * n + 9) ^ 12 := Nat.pow_le_pow_right (by omega) (by norm_num)
      omega
    omega
  have hbits := bits_len_le j
  have hQ : (9 * n + 9) ^ 12 ≤ 282429536481 * (n + 1) ^ 24 := by rw [nine_pow]; omega
  have hn24 : n ≤ (n + 1) ^ 24 := by
    have := Nat.le_self_pow (show (24 : ℕ) ≠ 0 by norm_num) (n + 1); omega
  rw [hT]
  unfold Qp roundPIn
  split_ifs
  · rw [frame_len]; have := w.wl; unfold CP; omega
  · rw [frame_len]; have := w.p3; unfold CP; omega
  · unfold CP; omega
  · rw [sgl_length]; unfold CP; omega
  · simp [CompareMachine.word]; unfold CP; omega
  · simp

end NearCubicWires.WireExponent3_5.UnionMachine.CWParFit
