import Proof.Packets.PhysicalIndexReload

/-! Three actual fixed-width copies overwrite reusable targets and restore
every head. The source words and width template are retained literally. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalTripleCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
noncomputable section

def machine := Composition.machine (PhysicalIndexReload.move (0 : Fin 7) .right)
  (Composition.machine (PhysicalCopyInto.machine (0 : Fin 7) 1 4)
    (Composition.machine (PhysicalCopyInto.machine (0 : Fin 7) 2 5)
      (Composition.machine (PhysicalCopyInto.machine (0 : Fin 7) 3 6)
        (PhysicalIndexReload.move (0 : Fin 7) .left))))

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalTripleCopy
