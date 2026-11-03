import Proof.Packets.PacketsXLiteralCacheReuse
import Proof.Packets.PhysicalIndexReload

/-! The actual reflected-cache refill with a uniform head-zero boundary for
every private tape. The retained common reserve driver alone stays at head1. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheTransaction
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open Theorem25Completion.CycleLiteralPairCost

def movePorts : Fin 2→Fin 68 := ![1,61]
noncomputable def move (d : HeadMove) := RecoveryFocus.machine movePorts (Completion.PhysicalDriverMoves.machine 2 d)
noncomputable def machine := Composition.machine (move .right)
  (Composition.machine LiteralCacheReuse.machine (move .left))

end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralCacheTransaction
