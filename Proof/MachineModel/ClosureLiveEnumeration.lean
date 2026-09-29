import Proof.CaseAnalysis.FinalSupplierRowInput

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.LiveEnumeration
open RepairSource.CloseoutFinal.C10SupplierRowInput
open SharedNormalizedEstimatorProgram CanonicalRecoveryLanguage
open scoped BigOperators

def binary (K : Nat) : List (BitInput K) := List.ofFn (fourfoldInputFinEquiv K).symm

end NearCubicWires.P1Closure.LiveEnumeration
