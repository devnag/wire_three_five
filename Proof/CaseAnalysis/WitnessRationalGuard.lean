import Proof.CaseAnalysis.WitnessAliases

/-! Move the fixed rational bit policy ahead of canonical reduction. The
early test reads only the original integer/natural fields. Exact re-encoding
proves that no accepted canonical coefficient is lost on any raw code. -/
namespace NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGuard
open CanonicalBinary CanonicalWitnessCodec
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true


theorem bit_cap_numeric (C a : ℕ) (hC : 0 < C)
    (h : natBitLength a ≤ natBitLength C) : a < 2 * C := by
  have hp : 2 ^ natBitLength C ≤ 2 * C := by
    unfold natBitLength
    rw [pow_succ, Nat.mul_comm]
    exact Nat.mul_le_mul_left 2 (Nat.pow_log_le_self 2 hC.ne')
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two a).trans_le
    ((Nat.pow_le_pow_right (by decide : 0 < 2) h).trans hp)

end NearCubicWires.RepairOrdinary.CloseoutWitness.RationalGuard
