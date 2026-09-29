import Proof.CaseAnalysis.WitnessMassPolicy
import Proof.CaseAnalysis.WitnessMassTail

/-! Prepare one absolute coefficient directly from the retained checked
binary numerator and denominator. The native addition bank is reused. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassPrepare
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold CompetitorReusableDecision CompetitorRationalDecision
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 94) : Fin 103:=i.castAdd 9
def zeroSlots : Fin 5→Fin 103:=![6,96,2,97,98]
def numSlots : Fin 5→Fin 103:=![6,94,3,99,100]
def denSlots : Fin 5→Fin 103:=![84,95,5,101,102]
def clear:=RecoveryFocus.machine old (clearProgram workSlot)
def zero:=RecoveryFocus.machine zeroSlots ClockNormalize.machine
def num:=RecoveryFocus.machine numSlots ClockNormalize.machine
def den:=RecoveryFocus.machine denSlots ClockNormalize.machine
def firstThree:=Composition.machine (Composition.machine clear zero) num
def machine:=Composition.machine firstThree den


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassPrepare
