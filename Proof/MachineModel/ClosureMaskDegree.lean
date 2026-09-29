import Proof.MachineModel.ClosureRadixCoordinate

/-! A.12's per-monomial degree, supplied by the actual mask bank. The
physical mask/cursor machines are unchanged. No degree bound on arbitrary
unrelated masks is assumed. -/
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
namespace NearCubicWires.RepairOrdinary
open RepairRepresentation SupplierPipeline SupplierPrime SupplierEstimator ThresholdCompiler

def P1Radix.effectiveDegree {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs] :=
  min (P1Radix.degree gs) gs.length

class P1MaskDegree {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]
    (rows : List (List Bool)) : Prop where
  bound : ∀ row∈rows, row.count true ≤ P1Radix.effectiveDegree gs

class P1BankDegree {n : Nat} (gs : List (ExactThresholdGate n)) [P1Radix gs]
    (bank : List (List (List Bool))) : Prop where
  bound : ∀ rows∈bank, P1MaskDegree gs rows

namespace P1MaskDegree

end P1MaskDegree

end NearCubicWires.RepairOrdinary
