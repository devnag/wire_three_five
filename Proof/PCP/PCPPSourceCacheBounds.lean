import Proof.PCP.PCPPSourceCachePrepare

/-! A fixed polynomial pays the one faithful PCPP call and complete shared
cache setup. The original native emitter and row loops retain separate costs. -/
namespace NearCubicWires.RepairOrdinary.PCPPSourceCache
open LocalBitMultitape RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def totalDegree (a : PointwisePCPPAlgorithm) := max (PCPPRequestRuntime.sourceDegree a) (degree a+1)
def coefficient (a : PointwisePCPPAlgorithm) := PCPPRequestRuntime.sourceCoefficient a+
  PCPPQueryCold.coefficient (degree a) (PCPPQueryCachedBounds.coefficient a)+1
def totalBudget (a : PointwisePCPPAlgorithm) (r : PCPPRequest a.minimumArity) :=
  coefficient a*(PCPPRequestRuntime.sourceParameter r.circuit)^(totalDegree a)

private theorem sum_bound (M L e f I J : ℕ) (hM : 1 ≤ M) (hL : L ≤ M) :
    I*M^e+1+J*L^f ≤ (I+J+1)*M^(max e f) := by
  have he:=Nat.pow_le_pow_right hM (show e ≤ max e f from Nat.le_max_left _ _)
  have hf:=(Nat.pow_le_pow_left hL f).trans
    (Nat.pow_le_pow_right hM (show f ≤ max e f from Nat.le_max_right _ _))
  have hi:=Nat.mul_le_mul_left I he
  have hj:=Nat.mul_le_mul_left J hf
  have hone : 1 ≤ M^(max e f) := Nat.one_le_pow _ _ hM
  nlinarith

theorem charge_bound (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    PCPPRequestRuntime.sourceCoefficient a*
      (PCPPRequestRuntime.sourceParameter request.circuit)^(PCPPRequestRuntime.sourceDegree a)+1+
      setupBudget a request ≤ totalBudget a request := by
  exact sum_bound _ _ _ _ _ _
    (by unfold PCPPRequestRuntime.sourceParameter; omega)
    (by unfold PCPPRequestRuntime.sourceParameter; omega)

theorem budget_bound (a : PointwisePCPPAlgorithm) (request : PCPPRequest a.minimumArity) :
    budget a request ≤ totalBudget a request := by
  have hs:=PCPPRequestRuntime.source_bound a request
  have hc:=charge_bound a request
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.PCPPSourceCache
