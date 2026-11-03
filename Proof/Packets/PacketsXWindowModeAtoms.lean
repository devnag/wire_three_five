import Proof.Packets.PacketsXWindowModeCacheDock
import Proof.Packets.ReusableNormalizedArithmetic
import Proof.Packets.PacketsXWindowLevelAtoms

/-! One fixed level-cache producer: emit both original-seed mode-cache halves,
then construct the reflected literal cache and its dense normalized atoms.
The execution of each constituent is discharged by its concrete run theorem. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairSource.VerifierDecoding
open CloseoutRowsModeCache
open CloseoutRowsRawPairSeek (Pair)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
noncomputable section

attribute [local irreducible] buildModeCache levelAtoms

def modeAtoms := Composition.machine buildModeCache levelAtoms

end
end PCJ9eff70d512234a4c_Fixed.Materializer.WindowProvider
