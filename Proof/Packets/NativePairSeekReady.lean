import Proof.CaseAnalysis.RowsRawPairSeek
import Proof.Packets.MaskProductReady

/-! The actual unary occurrence index seeks through resident native pairs;
its cursor is paid back to head one. This permits a descending literal-code
stream to access the original ascending atom cache without reordering data. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.NativePairSeekReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)

def slot : Fin 1→Fin 2 := ![0]
noncomputable def machine := Composition.machine CloseoutRowsRawPairSeek.loop
  (RecoveryFocus.machine slot PairCountReady.machine)

end PCJ9eff70d512234a4c_Fixed.Materializer.NativePairSeekReady
