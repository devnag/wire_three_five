import Proof.CaseAnalysis.FinalFuelRepin

namespace NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The defect: the POLYNOMIAL bucket can never hold one `2^q` call -/

/-! ## Section 2  The repair: the HOT bucket already holds it, and that is where it lands -/


end
end NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope
