import Proof.Packets.GradedWindowMachine

set_option autoImplicit false
set_option maxHeartbeats 650000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def raise := PhysicalIndexReload.move (7 : Fin 13) .right
def lower := PhysicalIndexReload.move (7 : Fin 13) .left
def machine := Composition.machine copyRoot (Composition.machine floor (Composition.machine raise
  (Composition.machine halves (Composition.machine lower (Composition.machine offset
    (Composition.machine clearValue clearQuotient))))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.GradedWindow
