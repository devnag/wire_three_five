import Proof.CaseAnalysis.WitnessMassPaddedCheck

/-! The sum's actual mass check uses the cleared term parser for constant
scratch and retains the same source, compact coefficient stream and Store. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.SumCheck
open LocalBitMultitape RecoveryRootRound CompetitorSumFold CompetitorThresholdAmbient
open CompetitorValidity (Estimate)
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def slots (i : Fin 110) : Fin 827:=⟨if i.val<94 then 725+i.val else i.val-94,by split_ifs <;> omega⟩
noncomputable def machine (k : ℕ) (q : ℚ):=RecoveryFocus.machine slots (MassCheck.machine k q)


end NearCubicWires.RepairOrdinary.CloseoutWitness.SumCheck
