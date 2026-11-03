import Proof.Packets.SubstitutionCallHeads
import Proof.Packets.SubstitutionScratchErase

/-! Actual output transfer and scratch erasure restore the reusable boundary. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding

noncomputable def copyResult := PhysicalCopyPair.machine (31 : Fin 44) 39 26 40 27
noncomputable def finish := Composition.machine copyResult
  (Composition.machine (moveDrivers .left) SubstitutionScratch.machine)

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
