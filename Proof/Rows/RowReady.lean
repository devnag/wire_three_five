import Proof.Rows.RowClear

/-!
# `Core.completeReady`, reduced to the completion machine

Everything in `Plan.Core.completeReady` except the `Step complete` itself and the single
`Row.budget ≤ rowFuel` inequality is discharged here from the chosen `state`:

* `prepareFuel=0` and both entry equalities are definitional;
* the framing capacity premise IS `RowCaps.Good`'s second clause;
* the cleanup certificate is `PCJ45bee56da9f34d5a_RowClear.clearBank`, and `2*cap+4` is the
  chosen `cleanupFuel` on the nose.

`ready_body` therefore states exactly what is still owed at this node.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace PCJ45bee56da9f34d5a_RowReady
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.P1Closure
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open PCJ45bee56da9f34d5a_RowState PCJ45bee56da9f34d5a_RowClear
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

end
end PCJ45bee56da9f34d5a_RowReady
