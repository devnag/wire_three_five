import Proof.CaseAnalysis.WitnessTermBegin

/-! One successful circuit exit clears only the private circuit bank.
Its paid driver is separate from the circuit's internal capacity, so the
actual support bound, including retained erase logs, remains explicit. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitReset
open LocalBitMultitape RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def privateSlot (i : Fin 1697) : Fin 1703 :=
  ⟨if i.val<1 then i.val else if i.val<1673 then i.val+1 else
    if i.val<1686 then i.val+2 else if i.val<1691 then i.val+3 else
    if i.val<1694 then i.val+4 else i.val+6,by split_ifs <;> omega⟩
def scratch (i : Fin 1697) : Fin 2532 := ⟨827+(privateSlot i).val,by have h:=(privateSlot i).isLt;omega⟩
def slots (i : Fin 1699) : Fin 2532 :=
  if h : i.val<1697 then scratch ⟨i.val,h⟩ else ⟨i.val+833,by omega⟩

noncomputable def machine := RecoveryFocus.machine slots (RecoveryScratchErase.resetMachine 1697)

end NearCubicWires.RepairOrdinary.CloseoutWitness.TermCircuitReset
