import Proof.Assembly.SelectedFactorization

/-! The actual selected branch as three phases and its retained tail.
All layout and component definitions are transparent; the equality includes
the dependent state count. Sequential execution retains the consecutive banks. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJda54a286946142d3_BranchPhases
open NearCubicWires NearCubicWires.P1TopDown
open LocalBitMultitape ExtDecompositionBatch RepairOrdinary RecoveryRootRound
open RepairSource RepairSource.CloseoutFinal RepairSource.VerifierDecoding
open CloseoutRowsOriginalSchedule ControllerSelectedContinuation
noncomputable section

variable (sources : EightSources) {gamma : Real} (p : Parameters sources gamma)
  (k r scratch : Nat)

attribute [local irreducible] WorkspaceSelectedAdmission.originalTapes WorkspaceSelectedEntry.size

end
end PCJda54a286946142d3_BranchPhases
