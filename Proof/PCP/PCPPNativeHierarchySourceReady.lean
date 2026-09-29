import Proof.PCP.PCPPNativeHierarchyNodesReady

/-! Original hierarchy input to the single selected faithful source cache.
The separated hierarchy bound is retained in the actual execution fuel. -/
namespace NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
open LocalBitMultitape SourceInterfaces RepairSource RepairRepresentation RepairSource.ProjectionNormalization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

variable (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time)
def originalBudget (a : PointwisePCPPAlgorithm) {k : ℕ}
    (H : OrdinaryHierarchy (fun n=>n^(k+2))) (Cpad : ℕ) (hpad : k+3≤Cpad) (r : InputRequest)
    (oracle : BooleanCircuit (PCPPNativeHierarchyNodes.width source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2)) :=
  PCPPNativeClauseDescriptorConsumer.sourceBudget a
    (PCPPNativeHierarchyNodes.circuit source k H.coefficient Cpad (VerifierEncoding.code H.verifier) r.2 hpad oracle)
    (PCPPNativeHierarchyNodes.originalBudget source H Cpad r oracle)

end
end NearCubicWires.RepairOrdinary.PCPPNativeHierarchySource
