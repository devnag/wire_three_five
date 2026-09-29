import Proof.Rows.RowsInitLoopAux

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false

namespace RowsInit.LoopTable
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta RowsInit.LoopAux
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairOrdinary.RecoveryRootRound
noncomputable section

/-! ## 1. Docking a unary / word map into any bank -/

/-! ## 2. The eleven stages on the local layout -/



/-! ## 3. The run -/

/-- Frame bookkeeping: a port no slot of a stage touches keeps content and head. -/
macro "frm" f:ident : tactic => `(tactic| exact ($f _ (by decide)))

/-! ## 4. The cost: linear in `2^s` (table class) -/

end
end RowsInit.LoopTable
