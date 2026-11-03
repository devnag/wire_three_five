import Proof.Packets.PacketsXWindowModeAtoms
import Proof.Packets.WindowModeLevelDock
import Proof.Packets.PacketsXWindowProviderZeroRight

/-! A fixed, paid level provider. It clears the previous right operand,
derives the raw level from the retained successor tag, emits both mode-cache
halves, and constructs their literal cache and cumulative dense atom bank. -/
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
noncomputable section

attribute [local irreducible] zeroRight makeModeLevel modeAtoms

def levelProvider := Composition.machine zeroRight (Composition.machine makeModeLevel modeAtoms)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
