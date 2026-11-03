import Proof.MachineModel.ClosureCompactBounds
import Proof.CaseAnalysis.FinalSupplierFuel
import Proof.MachineModel.SourceEnvelope
import Proof.CaseAnalysis.RowsEstimatorDriverBounds

/-! Risk gate for the compact row. The actual table driver has one residual
factor; its other exponent is source-fixed once the original-cache envelope
is fixed. Preparation and reset capacities remain additive in Driver.value. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.CompactCost
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator
open RepairSource CloseoutFinal C10SupplierFuel CloseoutRowsEstimator
open CompactBounds

noncomputable def tableCoefficient (printer : WilliamsAlgorithm) (c : Nat) :=
  2*Driver.tableCoefficient printer*(c+3)^CompetitorCrossScheduler.exponent printer

end NearCubicWires.P1Closure.CompactCost
