import Proof.Wire_3_5.UnionMachine.FrontCostValBase

/-! # C6 front, the time (8): the chain after phase 2 and the front's cost, per branch (P3:3669-3691)

**`valid_ok`** (on the valid branch the decoded guess passes its atoms and grid signs, and its entries' word opens the
rest), **`nums_le`** (the numbers' caps bound the counts), **`rejECost_le`**, **`rejACost_le`**, **`restCostOf_le`** (the
chain after phase 2 costs at most `10^81·n^40 + 400·rOf + β` at `n = N + 2` on every branch, `β` C1's call's budget at
the width), **`costOf_le`** (past the onset the front's cost is at most `4N + 20` plus phase 1, phase 2 and the chain).

Paper quantity of the main types: the front's time against the input length, the loop's capacity and C1's call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostRun
open NearCubicWires NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.UnionMachine.FrontDecode
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontEntriesRef (entScan restAfter)

section Branch
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} 
 {ζ : ℚ} (h0 : 0 < ζ) (h1 : ζ < 1 / 2)

/-- **The numbers' caps bound the counts.** -/
theorem nums_le {cap Kb Db Cδ q sys aux cb : ℕ} (h : FrontCh3P.NumsCaps cap h0 h1 Kb Db Cδ q sys aux cb) :
    q ≤ cap ∧ sys ≤ cap ∧ aux ≤ cap ∧ cb ≤ cap ∧ Ledger.rowBSparse h0 h1 2 Cδ q ≤ cap ∧
      (sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q ≤ cap ∧ Kb * (q + 1) ^ Db ≤ cap := by
  have hc1 := h.hcE
  have hc2 := h.cc
  have hc3 := CompilerMachine.Pool.lt_pow_natBitLength cb
  rw [pow_succ] at hc2
  have hc4 := h.hq4
  have hc5 := h.hBc
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The entries fail**: the chain's cost. -/
theorem rejECost_le (Dw Kw Dl Kb Db Cδ q sys aux cb N : ℕ) (xs r : List Bool) (hx : xs.length ≤ N + 2)
    (hr : r.length ≤ N + 2) (hnums : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (h2W : 2 * (Kw * (q + 1) ^ Dw) + 2 ≤ N + 2) (hDb : Db ≤ N + 2)
    (hP1 : PCPSerializerCapacity.Power.budget Dw Kw q ≤ N + 2) (hP2 : PCPSerializerCapacity.Power.budget Dl 1 q ≤ N + 2)
    (ht : Ledger.rowBt h0 h1 q ≤ N + 2) :
    FrontSemRun.rejECost h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb xs r ≤ 10 ^ 31 * (N + 2) ^ 12 := by
  obtain ⟨a1, a2, a3, a4, a5, -, a7⟩ := nums_le h0 h1 hnums
  have b := FrontCostRest.ch3Cost_le h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb N xs r hx hr (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) hDb hP1 hP2 (by omega) ht
  have p1 : N + 2 ≤ (N + 2) ^ 12 := Nat.le_self_pow (by norm_num) _
  unfold FrontSemRun.rejECost
  omega

/-- **An atom fails**: the chain's cost. -/
theorem rejACost_le (m : Mode) (Dw Kw Dl Kb Db Cδ q sys aux cb N : ℕ) (xs r : List Bool) (hx : xs.length ≤ N)
    (hr : r.length ≤ N) (hnums : FrontCh3P.NumsCaps (2 * (Kw * (q + 1) ^ Dw) + 2) h0 h1 Kb Db Cδ q sys aux cb)
    (h2W : 2 * (Kw * (q + 1) ^ Dw) + 2 ≤ N + 2) (hDb : Db ≤ N + 2)
    (hP1 : PCPSerializerCapacity.Power.budget Dw Kw q ≤ N + 2) (hP2 : PCPSerializerCapacity.Power.budget Dl 1 q ≤ N + 2)
    (ht : Ledger.rowBt h0 h1 q ≤ N + 2) (hL : (q + 1) ^ Dl ≤ N + 2) :
    FrontSemRun.rejACost m h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb xs r ≤ 10 ^ 81 * (N + 2) ^ 40 := by
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := nums_le h0 h1 hnums
  have b := FrontCostRest.ch3Cost_le h0 h1 Dw Kw Dl Kb Db Cδ q sys aux cb N xs r (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) hDb hP1 hP2 (by omega) ht
  have b2 := FrontCostRest.atCost_le m r xs q ((sys + aux) * Ledger.rowBSparse h0 h1 2 Cδ q) ((q + 1) ^ Dl) N hr hx
    (by omega) (by omega) hL
  have hn : 1 ≤ N + 2 := by omega
  have p1 : N + 2 ≤ (N + 2) ^ 40 := Nat.le_self_pow (by norm_num) _
  have p12 : (N + 2) ^ 12 ≤ (N + 2) ^ 40 := Nat.pow_le_pow_right hn (by norm_num)
  unfold FrontSemRun.rejACost
  omega

end Branch

section Top

end Top

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostRun
