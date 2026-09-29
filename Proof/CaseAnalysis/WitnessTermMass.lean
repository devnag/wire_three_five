import Proof.CaseAnalysis.WitnessTermReset

/-! A checked term's retained numerator and denominator are the actual
mass operands. No coefficient record is serialized, copied, or reparsed. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.TermMass
open LocalBitMultitape RecoveryRootRound SignedSortKey CompetitorSumFold
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 105) : Fin 826:=⟨if i.val<94 then 725+i.val else
  if i.val=94 then 690 else if i.val=95 then 693 else if i.val<103 then 723+i.val
  else if i.val=103 then 720 else 721,by split_ifs <;> omega⟩
noncomputable def machine:=RecoveryFocus.machine slots MassReusableStep.machine


end NearCubicWires.RepairOrdinary.CloseoutWitness.TermMass
