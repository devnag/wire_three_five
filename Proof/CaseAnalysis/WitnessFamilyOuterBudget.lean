import Proof.CaseAnalysis.WitnessNativeBudget

/-! The actual enclosing cold family pays its already-checked native,
legal-policy and capacity/family continuations. Both powers precede k. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
open SourceInterfaces RepairSource RepairRepresentation ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open LocalBitMultitape RadixSemantics ExecutableInterfaces CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def outerBound (a : PointwisePCPPAlgorithm) (G D copies e E K den : ℕ) (delta : ℚ) (sym : Bool) (N : ℕ):=
  ColdLegal.tailBound source a G D copies e den delta sym N+tailBound source a G D copies E K delta N+4

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.ColdFamily
