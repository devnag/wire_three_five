import Proof.Circuits.DecompositionNativeMagnitude

/-! Paid local rewinds after parsing a native signed field. The original
source cursor and the real bit-count sentinel remain live. The Boolean
stream and sign/nonzero fields are ready for the shared serializer call. -/
namespace NearCubicWires.RepairOrdinary.DecompositionMagnitudeReady
open LocalBitMultitape RepairRepresentation SignedSortKey DecompositionNativeMagnitude
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem present_value (bits : List Bool) :
    DecompositionBitFields.present bits=decide (0<RadixSemantics.value bits) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    change (b || DecompositionBitFields.present bits)=decide (0<(b.toNat+2*RadixSemantics.value bits))
    rw [ih]
    cases b <;> simp

theorem native_present (n : ℕ) :
    DecompositionBitFields.present (binary (natBitLength n) n)=decide (0<n) := by
  rw [present_value]
  have hf : n<2^natBitLength n := Nat.lt_pow_succ_log_self (by decide) n
  rw [binary_value (natBitLength n) n hf]

def selected (i : Fin 9) := decide (i≠0 ∧ i≠3)

end NearCubicWires.RepairOrdinary.DecompositionMagnitudeReady
