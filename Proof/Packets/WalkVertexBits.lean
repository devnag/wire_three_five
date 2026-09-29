import Proof.Packets.WalkUnframe
import Proof.Rows.SourceDockCore

/-! Read the second coordinate before the first. This is the actual bit
order of the Toeplitz walk equivalence, before low-padding removal. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkVertexBits
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound Completion

def secondSlots : Fin 2→Fin 3:=![1,2]
def firstSlots : Fin 2→Fin 3:=![0,2]
noncomputable def second:=RecoveryFocus.machine secondSlots WalkUnframe.machine
noncomputable def first:=RecoveryFocus.machine firstSlots WalkUnframe.machine
noncomputable def machine:=Composition.machine second first

noncomputable def ready:=MaskedReset.machine machine (fun _=>true)

end Theorem25Completion.WalkVertexBits
