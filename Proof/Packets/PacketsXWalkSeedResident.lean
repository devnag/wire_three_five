import Proof.Packets.PacketsXWalkLabelDispatch
import Proof.Packets.WalkSeedBinary
import Proof.Packets.WalkSeedDecode
import Proof.Packets.WalkSeedReady
import Proof.Supplier.SupplierWalkBridge
import Proof.Packets.CycleFieldPrimitives

/-! The seed decoder executes directly on the resident canonical walk bank.
Coordinates, label cursor and reusable edge resources stay in their fixed ports. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 15000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedResident
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairOrdinary.SignedSortKey
noncomputable section

def slots : Fin 9→Fin 15:=![0,1,8,9,10,11,12,13,14]
def machine:=RecoveryFocus.machine slots WalkSeedDecode.machine

end
end Theorem25Completion.WalkSeedResident
