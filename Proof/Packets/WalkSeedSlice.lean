import Proof.Packets.WalkSeedPadding
import Proof.Packets.WalkVertexBits
import Proof.Rows.CycleHeadMove

/-! The paid Toeplitz seed splitter. Starting from the actual vertex bits and
rank template, it drops low padding and writes lower, upper and translation
bits in that order. No seed word or extra counter is supplied. -/
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 12000
set_option warningAsError true
namespace Theorem25Completion.WalkSeedSlice
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.RecoveryExecution
open NearCubicWires.RepairOrdinary.RecoveryRootRound Completion

def paddingSlots : Fin 2→Fin 5:=![1,0]
def lowerSlots : Fin 3→Fin 5:=![1,0,2]
def upperSlots : Fin 3→Fin 5:=![1,0,3]
def translationSlots : Fin 3→Fin 5:=![1,0,4]
def moveRank:=CycleHeadMove.machine (![.stay,.right,.stay,.stay,.stay])
noncomputable def skipPadding:=RecoveryFocus.machine paddingSlots WalkSeedPadding.machine
noncomputable def lower:=RecoveryFocus.machine lowerSlots WalkRawSegment.machine
noncomputable def upper:=RecoveryFocus.machine upperSlots WalkRawSegment.machine
noncomputable def translation:=RecoveryFocus.machine translationSlots WalkRawSegment.machine
noncomputable def machine:=Composition.machine
  (Composition.machine (Composition.machine (Composition.machine
    (Composition.machine moveRank skipPadding) lower) moveRank) upper) translation


end Theorem25Completion.WalkSeedSlice
