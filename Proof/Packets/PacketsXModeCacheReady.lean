import Proof.Packets.PacketsXModeCacheCommon
import Proof.Packets.PhysicalBankCopy
import Proof.Packets.PhysicalRepeatStep
import Proof.Rows.PhysicalFocusBoundary

/-! Complete reusable delta-cache call: physically clear the old output,
produce both original sibling/child halves, retain the actual child count,
and return the new source cursor. All protected parameter masters may have
common-R zero backing supplied by their actual producers. -/
set_option autoImplicit false
set_option maxHeartbeats 30000
set_option maxRecDepth 1000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheReady
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
attribute [local irreducible] ModeCacheCommon.delta RecoveryScratchErase.resetMachine


end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheReady
