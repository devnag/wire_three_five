import Proof.CaseAnalysis.WitnessNativeScreenBudget

/-! The original guarded native continuation consumes only its actual
source request; all internal short-field envelope premises are discharged. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def bound (a : PointwisePCPPAlgorithm) (D G copies : ℕ) (delta : ℚ) (S Z : ℕ):=
  NativeScreen.bound G Z+1+(NativeCache.bound a Z+1+SourcePolicy.envelope D copies delta S)+1

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativePipeline
