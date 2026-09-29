import Proof.Amplification.RecoveryUnpair

/-! The shared scalar supplier at the literal EncodedNPVerifier input ABI.
The clock is polynomial in encoded bit length, including code zero. -/
namespace NearCubicWires.RepairOrdinary.RecoveryUnpair
open LocalBitMultitape RadixSemantics
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem bits_value (code : Nat) : value code.bits = code := by
  have h (bits : List Bool) : value bits = CanonicalBinary.bitsValue bits := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simp only [value, CanonicalBinary.bitsValue, ih]
  exact (h code.bits).trans (CanonicalBinary.bitsValue_natBits code)

theorem bits_length (code : Nat) : code.bits.length ≤ natBitLength code := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  simpa [natBitLength, Nat.succ_eq_add_one] using
    (Nat.lt_pow_succ_log_self (b := 2) (by omega) code)

end NearCubicWires.RepairOrdinary.RecoveryUnpair
