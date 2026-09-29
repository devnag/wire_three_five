import Proof.CaseAnalysis.WitnessSupportDock
import Proof.CaseAnalysis.CloseoutWitnessColdOracleBudget

/-! Actual cold native execution has one source-fixed polynomial envelope
in the hierarchy's linear input scale, including malformed and size exits. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def parameterBound (T : ℕ):=HierarchyBudget.sizeBound source T+T+39*(2*T+5)^2+1
def bound (a : PointwisePCPPAlgorithm) (D G copies cutoff : ℕ) (delta : ℚ) (T : ℕ):=
  ColdOracle.bound source cutoff T+1+
    NativePipeline.bound a D G copies delta (ColdFamily.scale source a G D copies delta T) (parameterBound source T)+1

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdNative
