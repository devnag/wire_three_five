import Proof.Packets.PacketsGlueMetaMul

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
noncomputable section

theorem walk_pow_le (a : DecompositionAlgorithm) (r : Request) : 2 ^ walkLength a r ≤ r.smallSize a := by
  have key : ∀ q n x1 x2 x3 x4 x5 x6 : ℕ, x5 ≤ q + n + x1 + x2 + x3 + x4 + x5 + x6 + 1 := by intros; omega
  unfold Request.smallSize
  exact key _ _ _ _ _ _ _ _

/-! ## The stages -/

end
end NearCubicWires.PacketsGlue.RequestMeta

