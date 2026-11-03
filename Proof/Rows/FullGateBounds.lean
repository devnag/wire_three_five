import Proof.Rows.CellGate
import Proof.Rows.MinimumAssignment

/-! Generalize the inspected HardwireBounds arithmetic to any actual full mask.
No evaluator machine changes; the emitted minimizing assignment is an instance. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
namespace PCJ45bee56da9f34d5a_FullGateBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.P1Closure NearCubicWires.SupplierPipeline NearCubicWires.SupplierEstimator
open C10NaturalHardwireScore (positiveSum selectedSum)
open CloseoutRowsPoolMinimum (negSum liveSum)
open C10NaturalHardwireTarget (pPart nPart)
open OffsetSourceGate (items)
open scoped BigOperators
noncomputable section


def source {q : Nat} (g : NormalizedThresholdGate q) :=
  (List.ofFn g.weight).flatMap intWord++intWord (g.threshold-1)

end
end PCJ45bee56da9f34d5a_FullGateBounds
