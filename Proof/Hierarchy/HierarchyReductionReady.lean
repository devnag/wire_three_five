import Proof.Hierarchy.HierarchyReductionTime

/-! The actual padded-word execution is available directly at the proved
quasilinear fuel, with no cost-realization premise for a later consumer. -/
namespace NearCubicWires.RepairOrdinary.HierarchyReduction
open LocalBitMultitape
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def ordinaryBudget (k C Cpad : ℕ) (code x : List Bool) :=
  runtimeCoefficient k C Cpad code*(x.length+1)*PCPResourceLedger.q x.length^2

end NearCubicWires.RepairOrdinary.HierarchyReduction
