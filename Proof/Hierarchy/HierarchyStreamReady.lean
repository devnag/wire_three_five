import Proof.Hierarchy.HierarchyStreamScalars
import Proof.Hierarchy.HierarchyStreamCost

/-! The same-source stream prefix on literal hierarchy requests, with its
separated budget and exact request/width/query transport. The outer framing
allowance is recorded once for the eventual whole ordinary constructor. -/
namespace NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
open LocalBitMultitape RepairOrdinary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)

theorem hierarchy_dimensions {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    request k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)=HierarchyEncode.encode H Cpad r ∧
    R source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)=HierarchyProjection.width source H Cpad r.1 ∧
    Q source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2)=HierarchyProjection.queries source H Cpad r.1 := by
  have he := HierarchySourceInput.encoded_request H Cpad hpad r
  refine ⟨he,?_,?_⟩
  · dsimp only [R,request]
    rw [he]
    rfl
  · dsimp only [Q,request]
    rw [he]
    rfl

theorem framed_budget_eq {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) :
    HierarchyStreamCost.framedBudget source H Cpad r=
      4*(HierarchySourceInput.hierarchyInput H r).length+3+
        budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) := by
  obtain ⟨he,hR,hQ⟩ := hierarchy_dimensions source H Cpad hpad r
  dsimp only [HierarchyStreamCost.framedBudget,HierarchySourceInput.constructorBudget,budget]
  rw [he,hR,hQ]
  omega

end
end NearCubicWires.RepairSource.ProjectionNormalization.HierarchyStreams
