import Proof.MachineModel.TopDownSelectedAssembly
import Proof.MachineModel.TopDownAdmissionBudget
import Proof.MachineModel.TopDownWorkspaceSelectedProgram
import Proof.CaseAnalysis.FinalLedgerAssembly

/-! Runtime of the actual selected guarded worker. Paper A.8:2249–2307
and C.10:4280–4330 keep polynomial-in-N admission separate from the single
residual table factor. The continuation's own fuel bound remains explicit.
Its polynomial degree must be fixed before choosing the hierarchy index. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDown.SelectedRuntime
open RepairOrdinary RepairSource SourceInterfaces
open RepairSource.CloseoutFinal RepairSource.SelectedRecoveryIntegration
noncomputable section

def sigma (sources : EightSources) : Nat := 6+(fixedProjection sources).degrees.proofLog

def width {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (n : Nat) : Nat :=
  (outer sources C.k C.clock).result.pcp.nativeWidth n

def logarithm {sources : EightSources} {gamma : Real} {p : Parameters sources gamma}
    (C : SelectedAssembly.ContinuationData sources p) (n : Nat) : Nat := Nat.log 2 (width C n)+1

end
end NearCubicWires.P1TopDown.SelectedRuntime
