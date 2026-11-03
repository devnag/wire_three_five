import Proof.Packets.PacketsXModeCacheReady
import Mathlib.Data.Nat.Log
import Mathlib.Tactic
import Proof.Packets.PacketsXCycleDenseAtomCost

/-! The original mode-cache producer fits the already generated common
reserve. The hash capacity is exactly the resident scalar C+9. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheBounded
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch CloseoutRowsModeCache
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost
attribute [local irreducible] ModeCacheReady.machine

end PCJ9eff70d512234a4c_Fixed.Materializer.ModeCacheBounded
