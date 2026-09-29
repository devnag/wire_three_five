import Proof.CaseAnalysis.WitnessMassPaddedStep

/-! One reusable direct term-mass update, including the paid clear of its
seven normalizer scratch cells under the enclosing parser driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableStep
open LocalBitMultitape RecoveryRootRound RecoveryExecution SignedSortKey
open CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 103) : Fin 105:=i.castAdd 2
def eraseSlots (i : Fin 9) : Fin 105:=⟨96+i.val,by omega⟩
def first:=RecoveryFocus.machine old MassStep.machine
def last:=RecoveryFocus.machine eraseSlots (RecoveryScratchErase.resetMachine 7)
def machine:=Composition.machine first last

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassReusableStep
