import Proof.Amplification.RecoveryValuationWhole

/-! Uniform bound for the whole cold valuation gate and its literal parse
meaning. The finite numeric screen is recorded in cold-valuation-smoke1;
the bound below is a universal Lean theorem. -/
namespace NearCubicWires.RepairOrdinary.RecoveryColdValuation
open LocalBitMultitape RecoveryExecution RecoveryRootRound
open RepairSource.RecoveryOracle.CompactCertificate.Serialization
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem parser_budget (bits : List Bool) :
    RecoveryValuationCount.limit (width bits) (cap bits)≤512*(bits.length+1)^2 := by
  have hb : max 1 bits.length≤bits.length+1 := by omega
  have hs := Nat.pow_le_pow_left hb 2
  unfold RecoveryValuationCount.limit RecoveryValuationStream.budget cap RecoveryColdHeaderCap.limit
    width RecoveryColdHeader.width RecoveryColdWidth.width
  nlinarith only [hb,hs]

theorem cold_budget (bits word : List Bool) :
    coldBudget bits word≤67108864*(bits.length+1)^2+8*word.length+64 := by
  have hp := RecoveryColdPreliminary.budget_le bits word
  have hv := parser_budget bits
  unfold coldBudget
  nlinarith only [hp,hv]

end NearCubicWires.RepairOrdinary.RecoveryColdValuation
