import Proof.Wire_3_5.UnionMachine.PlanWBase

/-! # C6: leaf U's enclosing application with the union's own exponents

The plan of `WireExponent3_5UnionMachinePlanW` with the union's clock and source-work exponents chosen by the
front: `kclk = gateDver + e`, `a = kclk + 1`, the margin `e` an existential of the front residual at each literal set
(so the front author picks it without replanning). The union's own preprocessing includes v8's cold decoders, whose
polynomial degree is fixed before the hierarchy clock (base `CloseoutWitness.Oracle.budget_polynomial`: `(N+2)^25`;
the atom decoders' capacity `(ℓ+2)^26`), so the source-work exponent must exceed them; `C_clk = kclk + 2 > d_ver + 2`
(P3:3653-3655) still holds, and the leaf's type `UnionLeafF l` (`Σ kclk A a`) is unchanged.

Main statement: **`union_planW2 c1 dec fronts count acc facts : ∀ l, UnionLeafF l`** with
`fronts : ∀ l, Σ e, ∀ F, GateFreeOK l F → FrontsFWE e l F` (the margin per literal set: a stage whose degree depends
on `l`'s source or PCPP constants beyond `gateDver` picks a larger `e` at that `l`) and the setup residuals at every
margin. Paper quantity: `UnionLeafF l`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.RepairRepresentation NearCubicWires.ExtDecompositionBatch NearCubicWires.BlockPlatform
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.Bindings.CLW20Theorem113
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.PlanW Filter
open NearCubicWires.RecoveryScheduleEnvelope (oracleSizeBound)

/-! ## The union's exponents -/

section Consts

end Consts

/-! ## Layer A at margin `e` -/

section Leaf


end Leaf

/-! ## Layer B at margin `e` -/

section Front
end Front


section LeafB
variable (l : Literals)

/-- The ledger's width grows (`TimeBudget.growth`). -/
theorem tendsto_q {kclk : ℕ} {E : Envelope} (B : TimeBudget kclk E) : Tendsto B.q atTop atTop :=
  tendsto_atTop_atTop.2 fun m => B.growth m

end LeafB

end NearCubicWires.WireExponent3_5.UnionMachine.PlanW2
