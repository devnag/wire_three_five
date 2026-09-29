import Mathlib
import Proof.Packets.PacketsLayout
import Proof.Packets.PacketsNatSum
import Proof.Rows.Plan

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.Touch
open NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.PacketsGlue NearCubicWires.PacketsGlue.NatSum

section Steps

end Steps

/-! ## Loops -/

macro "tcfg_eq" : tactic => `(tactic| (congr 1 <;> first | rfl | omega | (congr 1 <;> omega)))

/-! ## One occurrence, all occurrences, the run -/

end NearCubicWires.PacketsGlue.Touch

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.SupplierTouching
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent
noncomputable section

/-! ## Two fields -/

/-- The two-field scanner entry. -/
def scanIn2 (e : ℕ) (f1 f2 : List Bool) : Fin (3 + e) → List Bool :=
  fun k => if k.val = 0 then f1 else if k.val = 2 then f2 else []

end
end NearCubicWires.PacketsGlue.RequestMeta

