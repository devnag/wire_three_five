import Proof.Rows.ResidueProductReady

/-! A complete width-only cost/cap specialization of the physical modular
product producer, including its paid left-factor widening. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ45bee56da9f34d5a_ResidueProductBounds
open NearCubicWires NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairSource.CloseoutFinal
open SignedSortKey RadixSemantics
noncomputable section

def resetCap (w : Nat):=32*(w+1)^2

end
end PCJ45bee56da9f34d5a_ResidueProductBounds
