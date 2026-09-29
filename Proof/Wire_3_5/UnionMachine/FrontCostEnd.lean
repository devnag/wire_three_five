import Proof.Wire_3_5.UnionMachine.FrontCostTW

/-! # C6 front, the time (5): the word program and the tail (P3:3669-3691, 3797-3811)

**`pwCost_le`** (the prefix, the numbers, the thresholds: a fixed numeral times a fixed power of `n`, plus the table
writer's cost), **`capWCost_le`** (the capacity writer: polynomial plus `100·rOf`, the loop's scratch capacity), **`endCost_le`**
(the end: the tail, the install, `2·rOf`: polynomial plus `3·` the word program plus `400·rOf`).

Paper quantity of the main types: the front's end time against the input length and the loop's capacity. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostEnd
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCostKit

section Pw
variable {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The word program's cost.** -/
theorem pwCost_le (W Kb Db aV bV aT bT q sys aux cb nTW n : ℕ) (hn : 1 ≤ n) (hW : W ≤ n) (hq : q ≤ n)
    (hsys : sys ≤ n) (haux : aux ≤ n) (hcb : cb ≤ n) (hB : Kb * (q + 1) ^ Db ≤ n) (hDb : Db ≤ n)
    (ht : Ledger.rowBt h0 h1 q ≤ n) :
    FrontPw.pwCost (2 * W + 2) h0 h1 Kb Db aV bV aT bT q sys aux cb nTW ≤ 10 ^ 12 * n ^ 4 + nTW := by
  have hb1 := FrontSemEv.nbl_le_self q
  have hb2 := C1Cnt.pow_nbl_le q
  have hr1 := FrontCostRest.readC_le q
  have hr2 := FrontCostRest.readC_le 3
  have hr3 := FrontCostRest.readC_le sys
  have hr4 := FrontCostRest.readC_le aux
  have hr5 := FrontCostRest.readC_le cb
  have hno : FrontTW.numOps.length ≤ 100 := by decide
  have hto : (FrontTW.thrOps aV bV aT bT).length ≤ 100 := by unfold FrontTW.thrOps; simp
  have hP : FrontPw.prefixCost q Db (Kb * (q + 1) ^ Db) (PrimAsm.UnaryPow.sq (2 * W + 2)) + 1 +
      (FrontTW.numCost (2 * W + 2) h0 h1 q sys aux cb (Kb * (q + 1) ^ Db) + 1 +
        (0 + 1 + (FrontTW.thrOps aV bV aT bT).length * (200 * ((2 * W + 2) + 2) * ((2 * W + 2) + 2) + 1))) ≤
      10 ^ 12 * n ^ 4 := by
    unfold FrontPw.prefixCost FrontTW.numCost FrontTW.readsCost PrimAsm.UnaryPow.sq
    exact np_fin hn (by c6np) (by norm_num) (by norm_num)
  unfold FrontPw.pwCost
  omega

end Pw

/-- **The capacity writer's cost**: polynomial plus `100·f·c·2^m`. -/
theorem capWCost_le (A m c f sqc : ℕ) (hc : 1 ≤ c) (hf : 1 ≤ f) :
    FrontCapW.capWCost A m c f sqc ≤ (4 * A + 40) * sqc + 33 * m + 11 * c + 11 * f + 100 + 100 * (f * (c * 2 ^ m)) := by
  unfold FrontCapW.capWCost
  generalize 2 ^ m = X
  have h1 : X ≤ c * X := Nat.le_mul_of_pos_left X hc
  have h2 : c * X ≤ f * (c * X) := Nat.le_mul_of_pos_left _ hf
  have e1 : c * (10 * (1 * X) + 11) = 10 * (c * X) + 11 * c := by ring
  have e2 : 3 * (0 + c * (1 * X) + 1) = 3 * (c * X) + 3 := by ring
  have e3 : f * (10 * (0 + c * (1 * X)) + 11) = 10 * (f * (c * X)) + 11 * f := by ring
  have e4 : 3 * (0 + f * (0 + c * (1 * X)) + 1) = 3 * (f * (c * X)) + 3 := by ring
  have e5 : 32 * (1 * X) = 32 * X := by ring
  rw [e1, e2, e3, e4, e5]
  omega

theorem capOf_le_rOf (cr K A q : ℕ) : FrontTail.capOf cr K A q ≤ FrontTail.rOf cr K A q := by
  unfold FrontTail.rOf
  have h : 1 ≤ (q + 6) * 1000 := by omega
  calc FrontTail.capOf cr K A q = 1 * FrontTail.capOf cr K A q := (one_mul _).symm
    _ ≤ (q + 6) * 1000 * FrontTail.capOf cr K A q := Nat.mul_le_mul_right _ h

/-- **The end's cost**: polynomial plus `400·rOf`. -/
theorem endCost_le (W nT crT KT AT q L n : ℕ) (hn : 1 ≤ n) (hW : W ≤ n) (hq : q ≤ n) (hL : L ≤ n)
    (hA : AT ≤ n) (hK : 1 ≤ KT) (hc : (q + 1) ^ AT * KT ≤ n) :
    FrontSemTW.endCost W nT crT KT AT q L ≤ 10 ^ 12 * n ^ 4 + 3 * nT + 400 * FrontTail.rOf crT KT AT q := by
  have hc1 : 1 ≤ (q + 1) ^ AT * KT := Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
  have hcw := capWCost_le AT (FrontTail.mOf crT q) ((q + 1) ^ AT * KT) ((q + 6) * 1000)
    (PrimAsm.UnaryPow.sq (2 * W + 2)) hc1 (by omega)
  have hm : FrontTail.mOf crT q ≤ n := by unfold FrontTail.mOf; omega
  have hcr := capOf_le_rOf crT KT AT q
  have hrr : (q + 6) * 1000 * ((q + 1) ^ AT * KT * 2 ^ FrontTail.mOf crT q) = FrontTail.rOf crT KT AT q := by
    unfold FrontTail.rOf FrontTail.capOf; ring
  have hrr' : (q + 6) * 1000 * ((q + 1) ^ AT * KT * 2 ^ FrontTail.mOf crT q) =
      (q + 6) * 1000 * ((q + 1) ^ AT * KT * 2 ^ FrontTail.mOf crT q) := rfl
  have hcw' : FrontCapW.capWCost AT (FrontTail.mOf crT q) ((q + 1) ^ AT * KT) ((q + 6) * 1000)
      (PrimAsm.UnaryPow.sq (2 * W + 2)) ≤ (4 * AT + 40) * PrimAsm.UnaryPow.sq (2 * W + 2) + 33 * FrontTail.mOf crT q +
        11 * ((q + 1) ^ AT * KT) + 11 * ((q + 6) * 1000) + 100 + 100 * FrontTail.rOf crT KT AT q := by
    have e : (q + 6) * 1000 * ((q + 1) ^ AT * KT * 2 ^ FrontTail.mOf crT q) = FrontTail.rOf crT KT AT q := hrr
    have e' : (q + 6) * 1000 * ((q + 1) ^ AT * KT * 2 ^ FrontTail.mOf crT q) =
        (q + 6) * 1000 * ((q + 1) ^ AT * KT * 2 ^ FrontTail.mOf crT q) := rfl
    calc _ ≤ _ := hcw
      _ = _ := by rw [← e]
  have hpoly : (4 * AT + 40) * PrimAsm.UnaryPow.sq (2 * W + 2) + 33 * FrontTail.mOf crT q +
      11 * ((q + 1) ^ AT * KT) + 11 * ((q + 6) * 1000) + 100 ≤ 10 ^ 9 * n ^ 4 := by
    unfold PrimAsm.UnaryPow.sq
    exact np_fin hn (by c6np) (by norm_num) (by norm_num)
  have hsq : 17 * PrimAsm.UnaryPow.sq (2 * W + 2) + 22 * L + 11 * W + 400 ≤ 10 ^ 9 * n ^ 4 := by
    unfold PrimAsm.UnaryPow.sq
    exact np_fin hn (by c6np) (by norm_num) (by norm_num)
  unfold FrontSemTW.endCost FrontTail.tailCost FrontInstall.installCost
  omega

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostEnd
