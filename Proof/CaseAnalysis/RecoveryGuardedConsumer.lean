import Proof.CaseAnalysis.RecoveryReferenceAppend

/-! Connect the executed framed-reference head to the literal next prefix
of compileGuardedAny, the selector used by both original field selections. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceAppend
open LocalBitMultitape SourceInterfaces RepairRepresentation Composition
open FinitePredicateCircuit BoundedOracleStructuralCircuit RecoveryBoundedNative
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem budget_cubic (ref limit W : ℕ) (hr : ref ≤ W) (hl : limit ≤ W) :
    budget ref limit (16384*(W+1)^2) ≤ 8388608*(W+1)^3 := by
  have h:=RecoveryBoundedNativeGuarded.budget_cubic limit W hl
  have power : W+1 ≤ (W+1)^3 := by nlinarith [Nat.zero_le (W*W),Nat.zero_le (W*W*W)]
  unfold budget
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedReferenceAppend
