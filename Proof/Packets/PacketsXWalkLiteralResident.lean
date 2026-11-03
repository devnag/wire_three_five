import Proof.Packets.PacketsXWalkLiteralPrepare
import Proof.Packets.CycleZeroAllocate

/-! A physical initial walk tuple: vertex words, transition labels and unary
masters are retained, while every scratch tape and the rewind log start empty.
A paid sweep creates the entire zero workspace, then positions the width head. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.WalkLiteralCold
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.ExtIncidence NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces NearCubicWires.SupplierToeplitz NearCubicWires.SupplierToeplitzCore NearCubicWires.SupplierWalkBridge
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion
noncomputable section

def residentSlots : Fin 10→Fin 15 := ![2,3,8,9,11,12,13,14,4,6]
def residentAllocate := RecoveryFocus.machine residentSlots (CycleFields.ZeroAllocate.machine 8)
def residentRaise := RecoveryFocus.machine (fun _ : Fin 1=>(5 : Fin 15)) (PhysicalDriverMoves.machine 1 .right)
def residentMachine := Composition.machine residentAllocate residentRaise

end
end Theorem25Completion.WalkLiteralCold
