import Proof.CaseAnalysis.WitnessTermMultiply

/-! Actual q0 and actual source clause bits produce the complete family
term cap. The source count is paid once; constant coefficient mass remains
a separate guard and is not multiplied by this term count. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermPolicy
open LocalBitMultitape RecoveryRootRound RepairSource CloseoutWitnessPolicy RepairRepresentation
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

def ceilSlots (i : Fin 16) : Fin 44:=i.castAdd 28
def multiplySlots (i : Fin 27) : Fin 44:=
  ⟨if i.val=0 then 16 else if i.val=17 then 14 else 17+i.val,by split_ifs <;> omega⟩
def first (delta : ℚ) (copies : ℕ):=RecoveryFocus.machine ceilSlots
  (TermCeil.machine (termNumerator delta copies) (termDenominator delta copies))
def second:=RecoveryFocus.machine multiplySlots TermMultiply.machine
def machine (delta : ℚ) (copies : ℕ):=Composition.machine (first delta copies) second
def budget (delta : ℚ) (copies q0 cb : ℕ):=
  TermCeil.budget (termNumerator delta copies) (termDenominator delta copies) q0+1+
    TermMultiply.budget cb (xorTermBound delta q0 copies)


end
end NearCubicWires.RepairOrdinary.CloseoutWitness.TermPolicy
