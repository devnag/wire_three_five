import Proof.CaseAnalysis.WitnessMassDimensions

/-! The complete common mass policy is physically produced once from the
exact paid term and coefficient caps, including its reusable erase driver. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassPolicy
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def old (i : Fin 10) : Fin 25:=i.castAdd 15
def slots (i : Fin 15) : Fin 25:=⟨if i.val=0 then 8 else 10+i.val,by split_ifs <;> omega⟩
def first:=RecoveryFocus.machine old MassWidth.machine
def second:=RecoveryFocus.machine slots MassDimensions.machine
def machine:=Composition.machine first second
def budget (T b : ℕ):=MassWidth.budget T b+1+MassDimensions.budget (CompetitorSumWidth.width T b)

end
end NearCubicWires.RepairOrdinary.CloseoutWitness.MassPolicy
