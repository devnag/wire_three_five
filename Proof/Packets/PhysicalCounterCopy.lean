import Proof.Packets.PhysicalIndexReload

/-! Retained unary masters are copied with both endpoint cursors at one.
The successor variant physically supplies the M+1 child/parent driver. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def machine {t : Nat} (width source target : Fin t) :=
  Composition.machine (PhysicalIndexReload.move source .left)
    (Composition.machine (PhysicalIndexReload.machine width source target) (PhysicalIndexReload.move source .right))
def successor {t : Nat} (width source target : Fin t) :=
  Composition.machine (machine width source target)
    (RecoveryFocus.machine (fun _ : Fin 1=>target) VectorCounter.increment)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
