import Proof.CaseAnalysis.RowsCountBinary
import Proof.MachineModel.ClockFloorLog
import Proof.Packets.VectorCounter
import Proof.PCP.ProjectionDimensionTemplate
import Proof.Rows.SourceDockCore
import Proof.Rows.PhysicalDriverMoves

/-! Actual logarithmic digit-width generation from the runtime unary count.
The count is first encoded, its binary length is scanned, and the floor log is
incremented. Zero follows the same physical program and produces width one. -/
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace Completion.SourceDigitWidth
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding
open PCJ9eff70d512234a4c_Fixed.Materializer

def logSlots : Fin 3→Fin 12:=![5,10,11]
def outSlot : Fin 1→Fin 12:=fun _=>10
noncomputable def countMachine:=TapeEmbedding.machine 2 CloseoutRowsCountBinary.machine
noncomputable def logMachine:=RecoveryFocus.machine logSlots ClockFloorLog.machine
noncomputable def bumpMachine:=RecoveryFocus.machine outSlot VectorCounter.increment
noncomputable def moveMachine:=RecoveryFocus.machine outSlot (PhysicalDriverMoves.machine 1 .left)
noncomputable def machine:=Composition.machine (Composition.machine
  (Composition.machine countMachine logMachine) bumpMachine) moveMachine


end Completion.SourceDigitWidth
