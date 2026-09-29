import Proof.Rows.RowState

/-!
# The cleanup certificate of one row

`Plan.ClearBank` is a bank equality certificate, not an assumed execution: it asks for a cap,
a log capacity, the logical words being erased, the reserve of each cleared port, and the two
bank equations relating the Framing stage's exit to the next row's entry.

Every one of those is fixed by the `state` of `PCJ45bee56da9f34d5a_RowState`:

* `cap := caps.copyCap` and `logCapacity := caps.copyCap+1`, so `logFits` is `le_refl`;
* `logical k` is the framed payload word `frame (Frame.fields printer d k)`, whose length is
  `2*(Frame.fields printer d k).length+1`, i.e. exactly what `RowCaps.Good` caps;
* the cleared ports are the whole payload block plus the TRUE unary driver at `drv` and the
  FALSE log at `lg`; the descriptor target and the copier counter are NOT swept, so
  `rowBudget` never charges `descriptorReserve`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_RowClear
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. Frame-bank projections -/

/-! ## 2. The cleared-bank projections of `Plan.clearInput` / `Plan.clearOutput` -/

/-! ## 3. The cleanup slots miss every retained port -/

/-! ## 4. The certificate -/

end
end PCJ45bee56da9f34d5a_RowClear
