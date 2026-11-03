import Proof.CaseAnalysis.FinalSupplierRowInput
import Proof.Amplification.CanonicalRecoveryLanguage
import Proof.MachineModel.SharedNormalizedEstimatorProgram

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.LiveEnumeration
open RepairSource.CloseoutFinal.C10SupplierRowInput
open SharedNormalizedEstimatorProgram CanonicalRecoveryLanguage
open scoped BigOperators

def binary (K : Nat) : List (BitInput K) := List.ofFn (fourfoldInputFinEquiv K).symm

theorem binary_word_order (K : Nat) : binary K = allBitInputs K := by
  apply List.ext_getElem
  · simp only [binary,allBitInputs,List.length_ofFn,List.length_map,List.length_range]
  · intro i hi hj
    simp only [binary,allBitInputs,List.getElem_ofFn,List.getElem_map,List.getElem_range]
    rfl

end NearCubicWires.P1Closure.LiveEnumeration
