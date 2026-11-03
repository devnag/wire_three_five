import Proof.Wire_3_5.UnionMachine.FrontCostRunBase
import Proof.CaseAnalysis.CaseTwoWholeBudget
import Proof.CaseAnalysis.CaseTwoWholeBudgetHierarchy
import Proof.PCP.PCPPNativeHierarchyEnvelope
import Proof.PCP.PCPPNativeSourceCost
import Proof.Wire_3_5.Recovery.CaseTwoPadGSource

/-! # C6 front, the time (9): the front's cost at the pinned setup (P3:3632-3691, 3797-3811)

**`obE`**/**`obc`** (the guessed-oracle PCPP check's exponents at the gate, functions of the literals only),
**`costDeg`** (the front's polynomial degree `max 40 (obE + 4)`), **`KfT`** (the time factor `81600000·2^{A_main} + 1`),
**`atomQ`** (every width-level quantity the chain's cost reads, one polynomial of the width; **`atoms_ev`**: at most `N`
past a threshold), **`time_ev`** (the clock's bits within `N + 2`), and **`cost_ev`**: when `costDeg + 1 ≤ kE`, past a
threshold and the onset, on every input and witness the front's cost is at most `KfT·(q+1)^7·(callBudget q + β(q))`,
`β` C1's call's budget at the width.

Paper quantity of the main type: the front's time against the per-call budget and C1's call (`FrontAtW3.costAcc`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontCostSUE
open NearCubicWires NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires.RepairRepresentation NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW2 NearCubicWires.WireExponent3_5.Ledger
open NearCubicWires.WireExponent3_5.UnionMachine.FrontCaps (PQ)
open NearCubicWires.Bindings.CLW20Theorem113 (InNTIME)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSemTopS
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf scanOK)
open Filter

theorem k4_le (K : ℕ) : 2 * (K * K * K * K) + 2 * K + 1 ≤ FrontSemCap2.PW K := by
  unfold FrontSemCap2.PW
  have h1 : K * K * K * K ≤ (K + 1) ^ 9 := by
    calc K * K * K * K ≤ (K + 1) * (K + 1) * (K + 1) * (K + 1) := by gcongr <;> omega
      _ = (K + 1) ^ 4 := by ring
      _ ≤ (K + 1) ^ 9 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have h2 : K + 1 ≤ (K + 1) ^ 9 := Nat.le_self_pow (by norm_num) _
  omega

/-- The front's closing arithmetic: a polynomial part within the per-call budget, the loop's scratch `400·RQ` and C1's
call fit `KfT·X·(callBudget + β)` for `X ≥ q + 1`. -/
theorem fin_le (P ba cb capv q Am X : ℕ) (hX : q + 1 ≤ X) (hP : P ≤ cb) (hcap : capv + 1 ≤ 34 * 2 ^ Am * cb) :
    P + 400 * (1000 * (q + 6) * capv) + ba ≤ (81600000 * 2 ^ Am + 1) * X * (cb + ba) := by
  have h1 : 1 ≤ X := by omega
  have e1 : (q + 6) * capv ≤ (6 * X) * (34 * 2 ^ Am * cb) := Nat.mul_le_mul (by omega) (by omega)
  have e2 : cb ≤ X * cb := Nat.le_mul_of_pos_left _ h1
  have e3 : ba ≤ X * ba := Nat.le_mul_of_pos_left _ h1
  have r1 : 400 * (1000 * (q + 6) * capv) = 400000 * ((q + 6) * capv) := by ring
  have r2 : 400000 * ((6 * X) * (34 * 2 ^ Am * cb)) = 81600000 * 2 ^ Am * (X * cb) := by ring
  have r3 : (81600000 * 2 ^ Am + 1) * X * (cb + ba) =
      81600000 * 2 ^ Am * (X * cb) + 81600000 * 2 ^ Am * (X * ba) + X * cb + X * ba := by ring
  have e4 : 400000 * ((q + 6) * capv) ≤ 400000 * ((6 * X) * (34 * 2 ^ Am * cb)) := Nat.mul_le_mul_left _ e1
  omega

section SUE

end SUE

end NearCubicWires.WireExponent3_5.UnionMachine.FrontCostSUE
