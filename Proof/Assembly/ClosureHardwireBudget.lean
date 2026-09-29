import Proof.Assembly.ClosureHardwireReusable

/-! A.12's hardwired-child preparation, including reusable scratch, has a
uniform quadratic source-size budget. The whole copied source suffix and
backing are bounded; the append output is deliberately outside that bound.
All C/D/E/R workspace premises of the executed reusable call are discharged. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.HardwireBudget
open LocalBitMultitape RepairOrdinary ExtDecompositionBatch
open RepairRepresentation RepairSource CloseoutFinal SupplierPipeline SupplierEstimator
open VerifierDecoding SignedSortKey
open scoped BigOperators

def C (w : Nat) := 8*w+12

end NearCubicWires.P1Closure.HardwireBudget
