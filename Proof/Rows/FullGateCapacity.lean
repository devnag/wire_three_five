import Proof.Rows.FullGateRun

/-! One noncircular polynomial cleanup reserve, independent of false padding
on the retained original source and minimizing assignment. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 550000
namespace PCJ45bee56da9f34d5a_FullGateCapacity
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairRepresentation NearCubicWires.RepairSource.CloseoutFinal
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.P1Closure
open PCJ45bee56da9f34d5a_FullGateBounds PCJ45bee56da9f34d5a_CellGatePalette
open scoped BigOperators
noncomputable section

def capacity (B q w : Nat) := 2048*(B+q+w+1)^2

end
end PCJ45bee56da9f34d5a_FullGateCapacity
