import Proof.CaseAnalysis.FinalResidualLeaves
import Proof.CaseAnalysis.FinalStageSeam
import Proof.CaseAnalysis.FinalTailCompose

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierFuel

open SelectedRecoveryIntegration SourceInterfaces
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain (workerBudget)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageSeam (stagedFuel dockedFuel)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailCompose (bodyThreeFuel)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## 1. Arithmetic: constants and the single residual factor -/

/-! ## 2. The supplier stage's fuel (paper A.8:2249-2307) -/

def stageExponent (driverCoeff driverExp tableCoeff tableExp rowExp : ℕ) : ℕ :=
  max (driverCoeff + driverExp) (max (rowExp + tableExp + tableCoeff) 2) + 2

/-! ## 3. The A.8 split of the composed worker budget -/

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierFuel
