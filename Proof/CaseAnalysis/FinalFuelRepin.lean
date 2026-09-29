import Proof.CaseAnalysis.FinalRecordPadding

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 2  Spending the residual table factor `2 ^ (q - kappa * L_q)` -/

/-! ## Section 3  The re-pinned fuel, its coefficient and its onset -/

/-! ## Section 4  `hrow` at the re-pinned fuel -/

/-! ## Section 5  The `Parts` instance at the re-pinned fuel -/

/-! ## Section 6  The seam: the re-pin is a MAJORANT -/

/-! ## Section 7  The payoff -/

open C10TailComposeUniform (records StageReady pcppOf)


end
end NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
