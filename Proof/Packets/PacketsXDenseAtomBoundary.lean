import Proof.Packets.DenseAtom
import Proof.Packets.DenseAtomMaterialize
import Proof.Packets.PacketsXCycleDenseAtomCost
import Proof.Packets.PhysicalIndexReload

/-! Actual paid cursor boundary for repeated dense literal materialization.
The reserve cursor remains at one; both loop counters return to zero. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
namespace PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomBoundary
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch
open CloseoutRowsRawPairSeek (Pair cacheWord)
open Theorem25Completion.CycleBounds Theorem25Completion.CycleDenseAtomCost

attribute [local irreducible] DenseAtomMaterialize.machine DenseAtomCold.machine

def movePorts : Fin 2→Fin 46 := ![44,45]
noncomputable def move (d : HeadMove) := RecoveryFocus.machine movePorts (Completion.PhysicalDriverMoves.machine 2 d)
noncomputable def machine := Composition.machine (move .right)
  (Composition.machine DenseAtomMaterialize.machine (move .left))
noncomputable def cold := Composition.machine (move .right)
  (Composition.machine DenseAtomCold.machine (move .left))

attribute [local irreducible] machine cold

end PCJ9eff70d512234a4c_Fixed.Materializer.DenseAtomBoundary
