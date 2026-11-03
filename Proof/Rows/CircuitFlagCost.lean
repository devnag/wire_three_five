import Proof.Rows.NativeCircuitCodec

/-! A uniform cubic request-byte cost for the actual reusable circuit callback.
It depends only on unreplicated native circuit bytes and input arity. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000
namespace PCJ45bee56da9f34d5a_CircuitFlagCost
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ45bee56da9f34d5a_UniformMinimumBounds
open PCJ45bee56da9f34d5a_NativeCircuitFlags (payload flags)
open PCJ45bee56da9f34d5a_CircuitFlagBank
noncomputable section

def uniform (B q : Nat) :=2*(B*(8*(B+1)+10)+14*(B+1)+B+25)+10*U B q (B+1)+
 2*(B+1)+10*B+PCJ45bee56da9f34d5a_NativeGateLoop.budget B B q+42

end
end PCJ45bee56da9f34d5a_CircuitFlagCost
