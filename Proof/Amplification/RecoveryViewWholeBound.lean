import Proof.Amplification.RecoveryViewWhole

/-! Uniform cold raw-view allocation bound, including the full retained
witness copy. Only canonical completeness will bound witness length by B. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdView
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem input_layout (bits word : List Bool) : input bits word=
    fun i : Fin 100=>if i.val=0 then frame bits else if i.val=1 then frame word else [] := by
  funext i
  fin_cases i <;> rfl

theorem cold_budget (bits word : List Bool) :
    coldBudget bits word≤134217728*(bits.length+1)^2+8*word.length+128 := by
  have hp := RecoveryColdValuation.cold_budget bits word
  have hb := bank_bound bits
  unfold coldBudget RecoveryColdValuation.resumedBudget
  nlinarith only [hp,hb]

end NearCubicWires.RepairOrdinary.RecoveryColdView
