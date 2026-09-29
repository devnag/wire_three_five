import Proof.CaseAnalysis.FinalFuelEnvelope

namespace NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable

open RepairOrdinary SourceInterfaces SelectedRecoveryIntegration
open RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairSource.CloseoutFinal.C10PartsSchedule
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelRepin
open NearCubicWires.RepairSource.CloseoutFinal.C10FuelEnvelope

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## Section 1  The residual table cell, as a per-call fuel -/

/-! ## Section 2  `hrow` with `cost` at the cell -/

/-! ## Section 3  The `Parts` instance with `cost` at the cell -/

/-! ## Section 4  Nothing already proved is lost -/

/-! ## Section 5  The payoff -/


end
end NearCubicWires.RepairSource.CloseoutFinal.C10CostAtTable
