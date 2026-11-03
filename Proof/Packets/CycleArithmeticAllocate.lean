import Proof.Packets.CycleCommonReserve
import Proof.Rows.PhysicalDriverMoves
import Proof.Packets.ReusableArithmeticCore

/-! Cold physical allocation of the reusable 34-tape arithmetic bank.
Only raw R is resident initially. Two unary-template runs generate both R+3
logs, and an executed common sweep writes all thirty zero-backed tapes. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Theorem25Completion.CycleArithmeticAllocate
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.ProjectionNormalization NearCubicWires.RepairSource
open PCJ9eff70d512234a4c_Fixed PCJ9eff70d512234a4c_Fixed.Materializer
open Completion CycleCommonReserve
noncomputable section


def templateSlots : Fin 3→Fin 35 := ![32,31,33]
def logSlots : Fin 3→Fin 35 := ![32,34,30]
def eraseSlots (i : Fin 32) : Fin 35 :=
  Fin.addCases (fun j : Fin 30=>j.castAdd 5) (![32,33] : Fin 2→Fin 35) i
def bootSlots : Fin 1→Fin 35 := ![31]
def templateMachine := RecoveryFocus.machine templateSlots (DimensionTemplate.machine false)
def logMachine := RecoveryFocus.machine logSlots (DimensionTemplate.machine false)
def eraseMachine := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 30)
def bootMachine := RecoveryFocus.machine bootSlots (PhysicalDriverMoves.machine 1 .right)
def machine := Composition.machine (Composition.machine
  (Composition.machine templateMachine logMachine) eraseMachine) bootMachine

end
end Theorem25Completion.CycleArithmeticAllocate
