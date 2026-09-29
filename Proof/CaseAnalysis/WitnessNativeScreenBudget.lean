import Proof.CaseAnalysis.WitnessSourcePolicyBudget

/-! The native size screen is paid even on rejection. Its actual stream,
counter and cap programs have one polynomial in their measured parameter. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
open SourceInterfaces RepairSource ProjectionNormalization PaddedRunnerBudgetClosure BudgetTools
open PCPPNativeResourceCost
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def bound (G Z : ℕ):=1024*Z^3+1+counterCoefficient*Z^12+1+
  (DimensionPolynomial.coefficient (OracleCap.degree G) 1*(Z+2)^(2*OracleCap.degree G+2)+4*Z+18)

end NearCubicWires.RepairOrdinary.CloseoutWitness.NativeScreen
