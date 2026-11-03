import Proof.Packets.BudgetCycleClass

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceBudget
open NearCubicWires NearCubicWires.Admission NearCubicWires.RuntimeShape
open NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierEstimator

noncomputable section

/-! ## 1. Class tuples -/

/-- The six numbers of one `InClasses` statement (the divisor, live scale and the two scales are shared). -/
structure CostCls where
  dP : ℕ
  hT : ℕ
  hS : ℕ
  cP : ℕ
  cT : ℕ
  cS : ℕ

/-- `x` lies in the class `c`. -/
def CostCls.In (c : CostCls) (m L n qn x : ℕ) : Prop :=
  InClasses c.dP c.hT c.hS m L n qn c.cP c.cT c.cS x

/-! ## 2. `V` and the workspace -/

/-- S's `V = cVc · tableClass L hV q` is in the table class alone. -/
theorem V_inClasses {dP hS m L n qn V cVc hV : ℕ} (hVc : V ≤ cVc * tableClass L hV qn) :
    InClasses dP hV hS m L n qn 0 cVc 0 V :=
  InClasses.table hVc

/-! ## 3. The family class and the per-call family fuel -/

/-- **The family class**: row count `N ≤ nC·(q+1)^nE`, widths `≤ xC·(n+1)^xE`, `V = cVc·tableClass L hV q`. -/
def famCls (printer : WilliamsAlgorithm) (cVc hV nC nE xC xE : ℕ) : CostCls :=
  ⟨nE + (nE + (xE + xE)), nE + hV, nE,
    (3*P1TopDownPaidPayload.tapes printer+6)*(nC*((2*P1TopDownPaidReusableReserves.coefficient printer+20)*1)) +
      (3*P1TopDownPaidPayload.tapes printer + 700)*((nC+1)*(xC+1)*(xC+1)),
    (3*P1TopDownPaidPayload.tapes printer+6)*(nC*((2*P1TopDownPaidReusableReserves.coefficient printer+20)*cVc)),
    0⟩

end
end NearCubicWires.SourceBudget

