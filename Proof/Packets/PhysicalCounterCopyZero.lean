import Proof.Packets.PhysicalCounterCopy

/-! Physical M+1 driver generation from a retained zero-head master. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroSuccessor {t : Nat} (width source target : Fin t) :=
  Composition.machine (PhysicalIndexReload.machine width source target)
    (RecoveryFocus.machine (fun _ : Fin 1=>target) VectorCounter.increment)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.PhysicalCounterCopy
