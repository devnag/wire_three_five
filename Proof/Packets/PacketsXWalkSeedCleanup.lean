import Proof.Packets.PacketsXWalkSeedResident
import Proof.Rows.PhysicalFocusBoundary

/-! The resident decoder's six temporary tapes are physically cleared for the
next vertex. Coordinates, rank template, label cursor and edge resources remain. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 15000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedCleanup
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierWalkBridge
open NearCubicWires.RepairOrdinary.SignedSortKey
open PCJ9eff70d512234a4c_Fixed
noncomputable section

def slots : Fin 8→Fin 15:=![8,9,11,12,13,14,4,6]
attribute [local irreducible] WalkSeedResident.machine RecoveryScratchErase.resetMachine

def machine:=RecoveryFocus.machine slots (CycleFields.Primitives.eraseMachine 6)

end
end Theorem25Completion.WalkSeedCleanup
