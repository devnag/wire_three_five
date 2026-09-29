import Proof.PCP.PCPPNativeHierarchyInput

/-! Literal hierarchy requests enter the same retained stream executor with
the original source-fixed separated bound; loading the oracle is linear. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
open LocalBitMultitape RepairSource RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : RepairSource.ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
theorem original_budget {k : ℕ} (H : OrdinaryHierarchy (fun n => n^(k+2)))
    (Cpad : ℕ) (hpad : k+3 ≤ Cpad) (r : InputRequest) (oracle : List Bool) :
    budget source k H.coefficient Cpad (VerifierEncoding.code H.verifier) (List.ofFn r.2) (H.time r.1).bits oracle=
      HierarchyStreamCost.framedBudget source H Cpad r+4*oracle.length+6 := by
  rw [HierarchyStreams.framed_budget_eq source H Cpad hpad r]
  unfold budget PCPPNativeInputFields.budget HierarchySourceInput.hierarchyInput
  simp only [RepairSource.frame]
  omega

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchy
