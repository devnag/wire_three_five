import Proof.CaseAnalysis.FinalThresholdEstimateRowJoin
import Proof.MachineModel.TopDownPaidReusableFamily

/-! Apply the completed physical hrow to both existing family consumers.
The list-to-payload equality is the explicit upstream semantic contract;
it does not supply an execution receipt or a row-loader callback. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1TopDownPaidReusable
open LocalBitMultitape RepairOrdinary RepairRepresentation ExtDecompositionBatch
open SupplierPipeline SupplierEstimator SourceInterfaces CanonicalFourfoldRowProgram
open RepairSource.CloseoutFinal.C10ExternalRowLoop
open RepairSource.CloseoutFinal.C10ThresholdEstimateRowJoin
open RepairSource.CloseoutFinal.C10ThresholdNaturalSum
open CloseoutFinalC10RowAnswerWord
open CloseoutFinalC10SupplierAccuracy (rowAnswer)
open P1TopDownPaidPayload (tapes)
attribute [local irreducible] machine CompetitorCrossScheduler.producer

noncomputable def outputSlot (a : WilliamsAlgorithm) : Fin (tapes a+1+2+4) :=
  ((0 : Fin 2).natAdd (tapes a+1)).castAdd 4

end NearCubicWires.P1TopDownPaidReusable
