import Proof.CaseAnalysis.WitnessTermRead

/-! The exact paid T and b produce the reusable mass widths, driver and
initial zero accumulator in one cold run. No mass-record stream is supplied. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.MassCold
open LocalBitMultitape RecoveryRootRound CompetitorSumFold
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def policySlots (i : Fin 25) : Fin 119:=i.castAdd 94
def nativeSlots (i : Fin 94) : Fin 119:=⟨if i.val=6 then 16 else if i.val=84 then 8
  else if i.val=90 then 23 else 25+i.val,by split_ifs <;> omega⟩
noncomputable def policy:=RecoveryFocus.machine policySlots MassPolicy.machine
noncomputable def boot:=RecoveryFocus.machine nativeSlots bootstrapProgram
noncomputable def machine:=Composition.machine policy boot
def budget (T b : ℕ):=MassPolicy.budget T b+1+bootstrapBudget (CompetitorSumWidth.width T b)

end NearCubicWires.RepairOrdinary.CloseoutWitness.MassCold
