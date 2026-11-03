import Proof.Packets.PacketsXLiteralPairUnary
import Proof.Rows.PhysicalDriverMoves
import Proof.MachineModel.ClosureLocalSupport
import Proof.Amplification.RecoveryScratchErase

/-! Reusable unary literal-pair emission. The append port is protected while
all 55 private tapes and the actual reset log are physically cleared. Unary
metadata are retained, and the descending index cursor returns to one. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
namespace PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairReusable
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open Completion
noncomputable section

def selected (i : Fin 58) : Bool := decide (i≠2)

def scratchSlots (i : Fin 56) : Fin 61 := ⟨i.val+3,by omega⟩
def eraseSlots : Fin 58→Fin 61 := Fin.addCases (m:=56) (n:=2) scratchSlots (![59,60])

def worker := TapeEmbedding.machine 2 (MaskedReset.machine LiteralPairUnary.machine selected)
def erase := RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 56)
def indexSlot : Fin 1→Fin 61 := ![1]
def left := RecoveryFocus.machine indexSlot (PhysicalDriverMoves.machine 1 .left)
def right := RecoveryFocus.machine indexSlot (PhysicalDriverMoves.machine 1 .right)
def machine := Composition.machine (Composition.machine (Composition.machine left worker) erase) right

end
end PCJ9eff70d512234a4c_Fixed.Materializer.LiteralPairReusable
