import Proof.Packets.WalkSeedReady

/-! Complete fixed nine-tape physical seed decoding from the two framed
vertex coordinates and the actual rank template. All other tapes are empty. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedDecode
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound Completion

attribute [local irreducible] WalkVertexBits.ready WalkSeedReady.machine

def slots : Fin 6→Fin 9:=![2,4,5,6,7,8]
noncomputable def vertex : Machine 9 8:=TapeEmbedding.machine 5 WalkVertexBits.ready
noncomputable def slice : Machine 9 19:=RecoveryFocus.machine slots WalkSeedReady.machine
noncomputable def machine : Machine 9 27:=Composition.machine vertex slice

end Theorem25Completion.WalkSeedDecode
