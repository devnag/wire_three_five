import Proof.Packets.ScalarFromCounter

/-! The delta window's actual binary width2W, obtained by two counted passes
on the retained W counter, with no precomputed doubled scalar. -/
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ScalarTwice
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine := Composition.machine ScalarFromCounter.machine ScalarFromCounter.count

end
end PCJ9eff70d512234a4c_Fixed.Materializer.ScalarTwice
