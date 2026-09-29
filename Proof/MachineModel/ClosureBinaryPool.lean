import Proof.MachineModel.ClosureLiveEnumeration
import Proof.MachineModel.ClosureCompactSharedInput
import Proof.CaseAnalysis.FinalSupplierTable

/-! A.12 enumerates every live assignment once; its column count is independent
of that enumeration order. This pool uses the physical binary order while
keeping the existing sentinel, offsets, raw bank and pool cardinality. The
exported equality is at the count consumer, not merely a list permutation.
-/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.BinaryPool
open RepairRepresentation RepairOrdinary SupplierPipeline SupplierEstimator SupplierPrinter
open ThresholdCompiler CanonicalFourfoldRowProgram RepairSource CloseoutFinal
open C10SupplierRowInput
open scoped BigOperators

noncomputable section
variable {q : Nat} (a : DecompositionAlgorithm) (live : Finset (Fin q))
  (occ : List (SupportedNormalizedGate q)) (s : Nat)

def assignmentAt (k : Nat) : BitInput live.card :=
  (LiveEnumeration.binary live.card).getD k (fun _ => false)

def poolFn (harity : (s+1)/2+s/2 = liveᶜ.card) (k : Nat) :
    ExactThresholdGate ((s+1)/2+s/2) :=
  castGate harity (hardwire live
    ((childList a live occ).getD (k % (childList a live occ).length) falseChild)
    (assignmentAt live (k / (childList a live occ).length)))

def pool (harity : (s+1)/2+s/2 = liveᶜ.card) : List (ExactThresholdGate ((s+1)/2+s/2)) :=
  falseGate ((s+1)/2+s/2) ::
    List.ofFn (fun k : Fin ((liveList live).length * (childList a live occ).length) =>
      poolFn a live occ s harity k.val)

theorem pool_length (harity : (s+1)/2+s/2 = liveᶜ.card) :
    (pool a live occ s harity).length = (C10SupplierRowInput.pool a live occ s harity).length := by
  simp only [pool,C10SupplierRowInput.pool,List.length_cons,List.length_ofFn]

end
end NearCubicWires.P1Closure.BinaryPool
