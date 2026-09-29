import Proof.CaseAnalysis.WitnessLegalBudget

/-! The actual native/cache continuation uses the existing measured-node
and faithful-source bounds, including framing of its real emitted nodes. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization
open PaddedRunnerBudgetClosure BudgetTools PCPPNativeResourceCost
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def bound (a : PointwisePCPPAlgorithm) (Z : ℕ) :=
  48*(counterCoefficient*Z^12)+cacheCoefficient a*(4098*Z^3)^cacheDegree a

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeCache
