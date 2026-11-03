import Proof.CaseAnalysis.WitnessGuardedGcd

/-! The runtime comparison field is exactly the fixed bit policy, truncated
to the actual raw-field width. This handles short and malformed inputs too. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
open LocalBitMultitape RecoveryExecution RecoveryRootRound
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_iff (bits a : ℕ) (hp : 1 ≤ bits) : natBitLength a ≤ bits ↔ a < 2^bits := by
  constructor
  · intro h
    exact (Nat.lt_pow_succ_log_self Nat.one_lt_two a).trans_le
      (Nat.pow_le_pow_right (by decide : 0 < 2) h)
  · intro h
    by_cases hz : a = 0
    · simpa [hz, natBitLength] using hp
    · have hl := Nat.log_lt_of_lt_pow hz h
      unfold natBitLength
      omega

end NearCubicWires.RepairOrdinary.CloseoutWitness.GcdGuard
