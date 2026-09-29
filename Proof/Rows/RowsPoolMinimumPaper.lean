import Proof.Assembly.RowProduction

/-! The actual ordered coordinate loop computes the paper's minimum live
score. This is the field identity needed at the transformed native threshold,
with the original gate and the physically supplied membership order. -/
namespace NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
open RepairRepresentation SupplierPipeline CloseoutRowsPoolWeight
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section
variable {q : ℕ}

def items (g : NormalizedThresholdGate q) (live : Finset (Fin q)) : List Item:=
  List.ofFn (fun i : Fin q=>(g.weight i,decide (i∈live)))

end
end NearCubicWires.RepairOrdinary.CloseoutRowsPoolMinimum
