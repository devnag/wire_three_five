import Proof.Packets.PacketsXWindowLiteralCacheDock
import Proof.Packets.PacketsXWindowDensePrepare
import Proof.Packets.PacketVector
import Proof.Packets.PhysicalIndexReload
import Proof.Packets.PhysicalZeroBank
import Proof.Packets.WindowProviderPorts

/-! Closed level preparation after the actual native mode cache is produced:
build the reflected literal codes, initialize physical dense-loop inputs,
and materialize their normalized atoms in the resident dense table. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsRawPairSeek (Pair cacheWord)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost


attribute [local irreducible] buildLiteralCache prepareDense buildDense
noncomputable def levelAtoms := Composition.machine buildLiteralCache
  (Composition.machine prepareDense buildDense)
attribute [local irreducible] levelAtoms

end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
