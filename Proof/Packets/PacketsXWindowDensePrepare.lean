import Proof.Packets.SubstitutionPrepareCopies
import Proof.Packets.WindowNativeDock
import Proof.Packets.WindowWorkspace
import Proof.Packets.PhysicalEraseInto
import Proof.Packets.PhysicalCopyInto
import Proof.Packets.PacketsXWindowDenseDock

/-! Dense-table input preparation from resident sources and arithmetic
masters. The population is physically copied to the counted-loop master. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)

noncomputable def prepareDense := Composition.machine Workspace.machine
  (Composition.machine (PhysicalEraseInto.machine (129 : Fin 256) 32 33)
    (PhysicalCopyInto.machine (31 : Fin 256) 184 129))

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
