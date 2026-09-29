import Proof.Circuits.DecompositionMagnitudeSerializer

/-! Polynomial budget in the physical native bit width. This bounds the
executed serializer/pair charges without expanding any magnitude to unary. -/
namespace NearCubicWires.RepairOrdinary.DecompositionAtom
open CanonicalBinary PCPSerializerMass
set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

theorem magnitude_bits (n : ℕ) : (encodeNat n).bits.length ≤ 3*(natBitLength n+1)^5 := by
  let w := natBitLength n
  have h := (nat_bits_width (encodeNat n)).trans (encodeNat_bits_le n)
  have hp : 1≤(w+1)^5 := Nat.one_le_pow 5 _ (by omega)
  have hm : 1+2*w^4*(w+1) ≤ 1+2*(w+1)^5 := by
    calc
      _ ≤ 1+2*(w+1)^4*(w+1) := by gcongr; omega
      _ = _ := by ring
  change (encodeNat n).bits.length ≤ 3*(w+1)^5
  change (encodeNat n).bits.length ≤ 1+2*w^4*(w+1) at h
  omega

end NearCubicWires.RepairOrdinary.DecompositionAtom
