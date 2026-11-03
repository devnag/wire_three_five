import Proof.Packets.PacketsXWindowLevelAtoms
import Proof.Packets.PacketsXWindowLiteralConsume
import Proof.Packets.PhysicalCopyInto

/-! Paid right-operand clearing before a new level-cache call. The two
actual copies retain the left operand, common resources, and every metadata
word, so a previous level's nonempty arithmetic result is permitted. -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option maxRecDepth 10000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
noncomputable section

def zeroRight := Composition.machine (PhysicalCopyInto.machine (31 : Fin 256) 0 26)
  (PhysicalCopyInto.machine (31 : Fin 256) 0 27)

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
