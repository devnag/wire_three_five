import Proof.Wire_3_5.UnionMachine.EwE
import Proof.Wire_3_5.UnionMachine.EwRecs
import Proof.Wire_3_5.Primitive.ThresholdWriter.Joins

/-! # C6, e/W_j, part 10: the stage's size bounds

At the THR call's numbers (`J = listJ A B_* K`, `t = listT A B_* K`), every quantity of the window block and of the
`e` phase is at most `Y = 10^4·(m+1)^6`, `m = M + A + B_* + K` (**`yb`**), so the capacity need is at most
`10^4·(Y+1)^2` and the cost at most `10^8·(Y+1)^3` (**`need_le`**, **`cost_le`**), polynomial in `m`.

Paper quantity: none (the time and capacity of the `e`/`W_j` stage, polynomial in the THR call's numbers). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.UnionMachine.EwSize
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.UnionMachine.EwLevel
open NearCubicWires.WireExponent3_5.UnionMachine.EwWin

theorem clog_le_self (y : ℕ) : Nat.clog 2 y ≤ y := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le

/-- The size measure `Y = 10^4·(m+1)^6`. -/
def yOf (m : ℕ) : ℕ := 10000 * (m + 1) ^ 6

/-- **Every quantity is at most `Y`.** -/
theorem yb (M A Bs K : ℕ) :
    let X := M + A + Bs + K + 1
    let J := Primitive.listJ A Bs K
    let t := Primitive.listT A Bs K
    let Y := yOf (M + A + Bs + K)
    M ≤ Y ∧ A ≤ Y ∧ Bs ≤ Y ∧ K ≤ Y ∧ J ≤ Y ∧ 2 ^ J ≤ Y ∧ t ≤ Y ∧ Bs * t ≤ Y ∧ Nat.sqrt (Bs * t) ≤ Y ∧
      twMax t (Nat.sqrt (Bs * t)) ≤ Y ∧ EwBin.wdOf M A K J t ≤ Y ∧ 8 * (K * A) ≤ Y ∧ 1 ≤ Y := by
  intro X J t Y
  have hX1 : 1 ≤ X := by omega
  have hMX : M ≤ X := by omega
  have hAX : A ≤ X := by omega
  have hBX : Bs ≤ X := by omega
  have hKX : K ≤ X := by omega
  have hY : Y = 10000 * X ^ 6 := rfl
  have p2 : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) X
  have p3 : X ^ 2 ≤ X ^ 3 := Nat.pow_le_pow_right hX1 (by norm_num)
  have p5 : X ^ 3 ≤ X ^ 5 := Nat.pow_le_pow_right hX1 (by norm_num)
  have p6 : X ^ 5 ≤ X ^ 6 := Nat.pow_le_pow_right hX1 (by norm_num)
  have e2 : X ^ 2 = X * X := by ring
  have e3 : X ^ 3 = X * X * X := by ring
  have e5 : X ^ 5 = X * X * X * X * X := by ring
  have e6 : X ^ 6 = X * X ^ 5 := by ring
  -- K·A·Bs ≤ X³, 2^J ≤ 18X³
  have hKAB : K * A * Bs ≤ X ^ 3 := by
    rw [e3]; exact Nat.mul_le_mul (Nat.mul_le_mul hKX hAX) hBX
  have hJp : 2 ^ J ≤ 18 * X ^ 3 := by
    have h := EwKit.pow_clog_le2 (8 * K * A * Bs + 1) (by omega)
    have e : 8 * K * A * Bs = 8 * (K * A * Bs) := by ring
    show 2 ^ Nat.clog 2 (8 * K * A * Bs + 1) ≤ 18 * X ^ 3
    have hx3 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ hX1
    omega
  have hJJ : J ≤ 2 ^ J := Nat.lt_two_pow_self.le
  -- t ≤ 8·K·A·J + 2 ≤ 148 X^5
  have hKA : K * A ≤ X ^ 2 := by rw [e2]; exact Nat.mul_le_mul hKX hAX
  have ht : t ≤ 148 * X ^ 5 := by
    have h1 : t ≤ 8 * K * A * J + 1 + 1 := by
      show Nat.clog 2 (8 * K * A * J + 1) + 1 ≤ 8 * K * A * J + 1 + 1
      have := clog_le_self (8 * K * A * J + 1)
      omega
    have h2 : K * A * J ≤ X ^ 2 * (18 * X ^ 3) := Nat.mul_le_mul hKA (le_trans hJJ hJp)
    have h3 : X ^ 2 * (18 * X ^ 3) = 18 * X ^ 5 := by ring
    have e : 8 * K * A * J = 8 * (K * A * J) := by ring
    have hx5 : 1 ≤ X ^ 5 := Nat.one_le_pow _ _ hX1
    omega
  have hBt : Bs * t ≤ 148 * X ^ 6 := by
    have := Nat.mul_le_mul hBX ht
    have e : X * (148 * X ^ 5) = 148 * X ^ 6 := by ring
    omega
  have hs : Nat.sqrt (Bs * t) ≤ Bs * t := Nat.sqrt_le_self _
  have hx6 : 1 ≤ X ^ 6 := Nat.one_le_pow _ _ hX1
  have hwd : EwBin.wdOf M A K J t ≤ 400 * X ^ 6 := by
    unfold EwBin.wdOf
    have h1 : t * M ≤ 148 * X ^ 6 := by
      have := Nat.mul_le_mul ht hMX
      have e : 148 * X ^ 5 * X = 148 * X ^ 6 := by ring
      omega
    omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, ?_, by omega,
    by omega, by omega⟩
  unfold twMax
  omega

/-- The block's need in `Y`. -/
theorem winNeed_le (M A Bs K : ℕ) :
    EwRecs.winNeed (Primitive.listT A Bs K) Bs (Primitive.listJ A Bs K) ≤
      10000 * (yOf (M + A + Bs + K) + 1) * (yOf (M + A + Bs + K) + 1) := by
  obtain ⟨hM, hA, hB, hK, hJ, hJp, ht, hBt, hs, htw, hwd, hKA, hY1⟩ := yb M A Bs K
  unfold EwRecs.winNeed
  generalize yOf (M + A + Bs + K) = Y at *
  generalize Primitive.listT A Bs K = t at *
  generalize Primitive.listJ A Bs K = J at *
  have hL := EwRecs.recsDown_length_bound t (Nat.sqrt (Bs * t)) J J
  have hBt' : Bs * t = t * Bs := Nat.mul_comm _ _
  rw [Nat.mul_comm Bs t] at hs htw hBt hL
  have hL' : (recsDown t (Nat.sqrt (t * Bs)) J J).length ≤ Y * (5 * Y + 5) :=
    le_trans hL (Nat.mul_le_mul hJ (by omega))
  have hp : 2 ^ (J + 1) = 2 * 2 ^ J := by rw [pow_succ]; ring
  have hsq : 2 * (t * Bs + 2) * (t * Bs + 2) ≤ 2 * (Y + 2) * (Y + 2) := by gcongr
  rw [Nat.mul_comm Bs t]
  nlinarith

/-- The phase's need in `Y`. -/
theorem eNeed_le (M A Bs K : ℕ) :
    EwE.eNeed M A K (Primitive.listJ A Bs K) (Primitive.listT A Bs K) ≤
      10000 * (yOf (M + A + Bs + K) + 1) * (yOf (M + A + Bs + K) + 1) := by
  obtain ⟨hM, hA, hB, hK, hJ, hJp, ht, hBt, hs, htw, hwd, hKA, hY1⟩ := yb M A Bs K
  unfold EwE.eNeed EwBin.zOf
  generalize yOf (M + A + Bs + K) = Y at *
  nlinarith

/-- The block's cost in `Y`. -/
theorem winCost_le (M A Bs K : ℕ) :
    EwRecs.winCost (Primitive.listT A Bs K) Bs (Primitive.listJ A Bs K) ≤
      10 ^ 7 * (yOf (M + A + Bs + K) + 1) * (yOf (M + A + Bs + K) + 1) * (yOf (M + A + Bs + K) + 1) := by
  obtain ⟨hM, hA, hB, hK, hJ, hJp, ht, hBt, hs, htw, hwd, hKA, hY1⟩ := yb M A Bs K
  unfold EwRecs.winCost lvCost twCost
  generalize yOf (M + A + Bs + K) = Y at *
  generalize Primitive.listT A Bs K = t at *
  generalize Primitive.listJ A Bs K = J at *
  have hL := EwRecs.recsDown_length_bound t (Nat.sqrt (Bs * t)) J J
  rw [Nat.mul_comm Bs t] at hs htw hBt hL
  rw [Nat.mul_comm Bs t]
  generalize Nat.sqrt (t * Bs) = s at *
  generalize twMax t s = w at *
  have hL' : (recsDown t s J J).length ≤ Y * (5 * Y + 5) := le_trans hL (Nat.mul_le_mul hJ (by omega))
  generalize (recsDown t s J J).length = L at *
  generalize t * Bs = x at *
  generalize 2 ^ J = p at *
  have c1 : 1000 * (x + 2) * (x + 2) * (x + 2) ≤ 1000 * (Y + 2) * (Y + 2) * (Y + 2) := by gcongr
  have c2 : 40 * (Bs + 1) * (t + 1) ≤ 40 * (Y + 1) * (Y + 1) := by gcongr
  have c3 : 2000 * (t + s + J + p + 2) * (t + s + J + p + 2) ≤ 2000 * (4 * Y + 2) * (4 * Y + 2) := by
    gcongr <;> omega
  have c4 : 1000 * (w + 1) * (w + 2) ≤ 1000 * (Y + 1) * (Y + 2) := by gcongr
  have c5 : J * (2000 * (t + s + J + p + 2) * (t + s + J + p + 2) + 1000 * (w + 1) * (w + 2) +
      40 * (5 * w + 2) + 3 * (5 * w + 2) + 200 + 2) ≤
      Y * (2000 * (4 * Y + 2) * (4 * Y + 2) + 1000 * (Y + 1) * (Y + 2) + 40 * (5 * Y + 2) + 3 * (5 * Y + 2) + 200 + 2) := by
    apply Nat.mul_le_mul hJ
    omega
  nlinarith

/-- The phase's cost in `Y`. -/
theorem eCost_le (M A Bs K : ℕ) :
    EwE.eCost M A K (Primitive.listJ A Bs K) (Primitive.listT A Bs K) ≤
      10 ^ 7 * (yOf (M + A + Bs + K) + 1) * (yOf (M + A + Bs + K) + 1) * (yOf (M + A + Bs + K) + 1) := by
  obtain ⟨hM, hA, hB, hK, hJ, hJp, ht, hBt, hs, htw, hwd, hKA, hY1⟩ := yb M A Bs K
  unfold EwE.eCost EwBin.zOf RegRat.mulCost
  generalize yOf (M + A + Bs + K) = Y at *
  generalize Primitive.listT A Bs K = t at *
  generalize Primitive.listJ A Bs K = J at *
  generalize EwBin.wdOf M A K J t = w at *
  generalize 8 * (K * A) = c at *
  calc _ ≤ 500 * (3 * Y + 1) * (3 * Y + 1) + 600 * (4 * Y + 2) * (4 * Y + 2) +
        (2 * Y * (Y * (82 * Y + 32) + 133 * Y + 15 + 41 * Y + 12) + 40 * Y + 10) +
        (2 * (Y * (82 * Y + 32) + 133 * Y + 15) + 100 * Y + 20) + (Y * (100 * Y + 22) + 50 * Y + 20) +
        (3 * Y + 1) + 5 := by gcongr <;> omega
    _ ≤ _ := by nlinarith [Nat.zero_le (Y * Y * Y), Nat.zero_le (Y * Y)]

theorem y_le (m : ℕ) : yOf m + 1 ≤ 10001 * (m + 1) ^ 6 := by
  unfold yOf
  have : 1 ≤ (m + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  omega

/-- **The stage's capacity need**, polynomial. -/
def ewNeed (m : ℕ) : ℕ := 10 ^ 13 * (m + 1) ^ 12

/-- **The stage's time bound**, polynomial. -/
def ewBound (m : ℕ) : ℕ := 10 ^ 21 * (m + 1) ^ 18

theorem sq_y (m : ℕ) : 10000 * (yOf m + 1) * (yOf m + 1) ≤ ewNeed m / 2 := by
  have h := y_le m
  unfold ewNeed
  have hP : (m + 1) ^ 12 = (m + 1) ^ 6 * (m + 1) ^ 6 := by ring
  rw [hP]
  generalize (m + 1) ^ 6 = P at *
  generalize yOf m + 1 = Y at *
  have h2 := Nat.mul_le_mul h h
  have e1 : 10000 * Y * Y = 10000 * (Y * Y) := by ring
  have e2 : 10001 * P * (10001 * P) = 100020001 * (P * P) := by ring
  rw [e1]
  omega

theorem cube_y (m : ℕ) : 10 ^ 7 * (yOf m + 1) * (yOf m + 1) * (yOf m + 1) ≤ ewBound m / 4 := by
  have h := y_le m
  unfold ewBound
  have hP : (m + 1) ^ 18 = (m + 1) ^ 6 * (m + 1) ^ 6 * (m + 1) ^ 6 := by ring
  rw [hP]
  generalize (m + 1) ^ 6 = P at *
  generalize yOf m + 1 = Y at *
  have h3 := Nat.mul_le_mul (Nat.mul_le_mul h h) h
  have e1 : 10 ^ 7 * Y * Y * Y = 10 ^ 7 * (Y * Y * Y) := by ring
  have e2 : 10001 * P * (10001 * P) * (10001 * P) = 1000300030001 * (P * P * P) := by ring
  rw [e1]
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.EwSize
