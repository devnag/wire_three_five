import Proof.Packets.SubstitutionOuterStep
import Proof.Packets.PhysicalCopyPair
import Proof.Packets.PhysicalOneCount

/-! Physical preparation of source, both count drivers, and product one from
the current resident right operand. All destination backing was allocated by
SubstitutionScratch.run, and all operations have ordinary paid receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 350000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding



noncomputable def copyInput := PhysicalCopyPair.machine (31 : Fin 44) 26 37 27 43
noncomputable def copyWidth := PhysicalCopyPair.machine (31 : Fin 44) 24 35 24 38
noncomputable def makeOne := PhysicalOneCount.into (42 : Fin 44)
noncomputable def resetProduct := PhysicalCopyPair.machine (31 : Fin 44) 41 26 42 27
noncomputable def machine := Composition.machine copyInput
  (Composition.machine copyWidth (Composition.machine makeOne resetProduct))

end PCJ9eff70d512234a4c_Fixed.Materializer.SubstitutionCall
