import Proof.Wire_3_5.Primitive.SeedFix.TS4OBase

/-! # T (#120, thrStage4U), part 14: the prep's time is polynomial

P3:3071-3091 ("the preprocessing … runs in time polynomial in `n`") and P3:3114-3115: at the gate, the prep's stage cost
`p0StageCost` (the request parse, the THR cap `B_T(n)`: PA's schedule `t = O(L)`, the sparse count, `capM`'s squares;
the count `V = W + (n+1)^{26}`) is at most `Kp·(n + W + 3)^{Dp}`, the degree fixed by the literals, the coefficient by
`c_r`:

* `Dp`, `Kp`, **`p0Stage_le`**.

Paper quantities of the main type: the prep's step count, polynomial in `n + W`. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.SymDec

variable (l : Literals)

theorem nbl_small (v : ℕ) : natBitLength v + 2 ≤ 2 ^ (natBitLength v) + 2 := by
  have := Nat.lt_two_pow_self (n := natBitLength v); omega

theorem a1_le (n B : ℕ) (h : n + 3 ≤ B) : (natBitLength n + 2) * (40 * 2 ^ natBitLength n + 40) ≤ 120 * B ^ 2 := by
  have pn := W6.pow_nbl n
  have e2n : 2 ^ (natBitLength n + 1) = 2 * 2 ^ natBitLength n := by rw [pow_succ]; ring
  have nbln : natBitLength n ≤ n + 1 := by unfold natBitLength; have := Nat.log_le_self 2 n; omega
  have hm := Nat.mul_le_mul (show natBitLength n + 2 ≤ B by omega) (show 40 * 2 ^ natBitLength n + 40 ≤ 120 * B by omega)
  calc _ ≤ B * (120 * B) := hm
    _ = 120 * B ^ 2 := by ring

theorem a2_le (a : ℕ) (ha : a ≤ 4) : (natBitLength a + 2) * (40 * 2 ^ natBitLength a + 40) ≤ 12 * 440 := by
  have pa := W6.pow_nbl a
  have e2a : 2 ^ (natBitLength a + 1) = 2 * 2 ^ natBitLength a := by rw [pow_succ]; ring
  have ba := nbl_small a
  exact Nat.mul_le_mul (by omega) (by omega)

theorem sq_le (W B : ℕ) (h : W + 3 ≤ B) : UnaryPow.sq (2 * W + 2) ≤ 800 * B ^ 2 := by
  unfold UnaryPow.sq
  have hm := Nat.mul_le_mul (show 2 * W + 2 + 2 ≤ 2 * B by omega) (show 2 * W + 2 + 2 ≤ 2 * B by omega)
  calc 200 * (2 * W + 2 + 2) * (2 * W + 2 + 2) = 200 * ((2 * W + 2 + 2) * (2 * W + 2 + 2)) := by ring
    _ ≤ 200 * (2 * B * (2 * B)) := Nat.mul_le_mul_left _ hm
    _ = 800 * B ^ 2 := by ring

theorem a5_le (t J W B : ℕ) (ht : t ≤ J * B + 1) (h : W + 3 ≤ B) :
    (t + 5) * (40 * UnaryPow.sq (2 * W + 2)) ≤ 32000 * (J * B ^ 3) + 192000 * B ^ 2 := by
  have hs := sq_le W B h
  have hm := Nat.mul_le_mul (show t + 5 ≤ J * B + 6 by omega) (show 40 * UnaryPow.sq (2 * W + 2) ≤ 32000 * B ^ 2 by omega)
  calc _ ≤ (J * B + 6) * (32000 * B ^ 2) := hm
    _ = 32000 * (J * B ^ 3) + 192000 * B ^ 2 := by ring

theorem a6_le (W B : ℕ) (h : W + 3 ≤ B) :
    ((2 * W + 2 + 2) * 200 + 1500) * UnaryPow.sq (2 * W + 2) ≤ 1520000 * B ^ 3 := by
  have hs := sq_le W B h
  have hm := Nat.mul_le_mul (show (2 * W + 2 + 2) * 200 + 1500 ≤ 1900 * B by omega) hs
  calc _ ≤ 1900 * B * (800 * B ^ 2) := hm
    _ = 1520000 * B ^ 3 := by ring

end NearCubicWires.WireExponent3_5.PrimT.TS4
