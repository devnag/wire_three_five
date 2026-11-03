import Proof.Rows.ClosureOffsetSourceGateReusable

/-! Pin the executed native gate comparison to the paper's frozen C_i and
the count table's actual row/column convention. No alternative split is used. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.P1Closure.OffsetSourceGate
open RepairOrdinary RepairRepresentation RepairSource.CloseoutFinal SupplierPipeline SupplierEstimator
open RepairSource.CloseoutRowsUniversal CloseoutRowsPoolWeight
open scoped BigOperators

def items {q : Nat} (g : NormalizedThresholdGate q) (x : BitInput q) : List Item :=
  List.ofFn (fun i=>(g.weight i,x i))

end NearCubicWires.P1Closure.OffsetSourceGate
