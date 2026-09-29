import Proof.Amplification.RecoveryBoundedNativeLiteralRun

/-! Actual bounded-compiler literal emission starts with blank scratch.
The one retained capacity is supplied by the enclosing compiler allocator;
its size dominates every native-field printing bound uniformly. -/
namespace NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
open LocalBitMultitape RepairRepresentation RecoveryExecution PCPPNativeClauseBank
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem budget_bound (index position C : ℕ)
    (hi : PCPPNativeSumAppend.budget 0 index+1≤C) (hp : PCPPNativeSumAppend.budget 0 position+1≤C)
    (hz : PCPPNativeSumAppend.budget 0 0+1≤C) : budget index position C≤16*C+34 := by
  have h1 : (natWord 1).length=3 := by decide
  have h2 : (natWord 2).length=5 := by decide
  unfold budget firstBudget secondBudget nodeBudget PCPPNativeSumReusable.budget
  simp only [values,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,h1,h2]
  omega

end NearCubicWires.RepairOrdinary.RecoveryBoundedNativeLiteral
