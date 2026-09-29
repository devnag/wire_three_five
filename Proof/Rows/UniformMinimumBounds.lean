import Proof.Rows.UniformMinimumGate
import Proof.Rows.FullGateCapacity

/-! Uniform paid banks across all original gates of one request. A short linear
source/parser cap H, a quadratic evaluator reserve R, and larger cleanup U are
separate; no tape capacity depends on itself. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000
namespace PCJ45bee56da9f34d5a_UniformMinimumBounds
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.P1Closure NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open PCJ45bee56da9f34d5a_MinimumGateCell (minInput)
open scoped BigOperators
noncomputable section
attribute [local irreducible] PCJ45bee56da9f34d5a_CellGate.machine
attribute [local irreducible] PCJ45bee56da9f34d5a_MinimumGateCell.machine

def H (B q w : Nat) := 64*(B+q+w+1)
def R (B q w : Nat) := 1024*(B+q+w+1)^2
def U := PCJ45bee56da9f34d5a_FullGateCapacity.capacity

end
end PCJ45bee56da9f34d5a_UniformMinimumBounds
