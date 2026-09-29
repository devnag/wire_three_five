import Proof.PCP.PCPPSubstitutionCircuit
import Proof.PCP.PCPPRequestBounds

/-! The actual compact substituted circuit at the faithful pointwise source's
typed/code boundary. This module makes no claim of an ordinary byte producer. -/
namespace NearCubicWires.RepairOrdinary.PCPPSubstitution
open SourceInterfaces RepairRepresentation PCPPRequestBoundary
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def requestParameter (a : PointwisePCPPAlgorithm) (r q size : ℕ) :=
  q*(2*size+1)+3*(2*q)^3+2*domain a r+5

def sourceRequest (a : PointwisePCPPAlgorithm) {n r q : ℕ} (oracle : BooleanCircuit n)
    (projections : Fin q → Fin n → ProjectedRandomBit r) (formula : ThreeCNF q) :=
  request a (compactSubstituted oracle projections formula)

theorem sourceRequest_eval (a : PointwisePCPPAlgorithm) {n r q : ℕ}
    (oracle : BooleanCircuit n) (projections : Fin q → Fin n → ProjectedRandomBit r)
    (formula : ThreeCNF q) (input : BitInput (domain a r)) :
    (sourceRequest a oracle projections formula).circuit.eval input=
      formula.eval (fun j => oracle.eval (fun i =>
        (projections j i).eval (ProjectionPCPPadding.prefixBits (Nat.le_max_left r a.minimumArity) input))) := by
  unfold sourceRequest
  rw [request_eval,compactSubstituted_eval]

end NearCubicWires.RepairOrdinary.PCPPSubstitution
