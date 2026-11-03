import Proof.Packets.GradedWindowFromRoot

/-! Each level pays to erase the previous window counter before generating
its replacement, so a retained W master can be reused across descending levels. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def clearOutput := PhysicalCopyInto.machine (12 : Fin 13) 1 9
def reusable := Composition.machine clearOutput machine

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
