import Proof.Foundations.TseitinCNF

/-!
# Nested balanced CNF payload extension

This module carries the theory of the second additive SAT marker.  Its
definitions live beside `decodeBalancedCNF` in `Proof.Foundations.BalancedCNFCodec`,
because `Proof.Foundations.Semantics` must see the nested decoder to dispatch `.sat`
on the nested marker.  The outer balanced list contains one balanced
clause-code list per formula chunk.  Decoding validates both levels and
flattens only in the oracle semantics; no machine register contains the flat
list.
-/

namespace NearCubicWires.NestedBalancedCNFCodec

open NearCubicWires
open NearCubicWires.BalancedCNFSATEncoding
open NearCubicWires.CanonicalBinary

open private decodeClauseCodes from Statement

/-! ## Width of the two-level payload -/

private theorem pair_mono {left left' right right' : ℕ}
    (hleft : left ≤ left') (hright : right ≤ right') :
    Nat.pair left right ≤ Nat.pair left' right' := by
  calc
    Nat.pair left right ≤ Nat.pair left' right := by
      rcases hleft.eq_or_lt with h | h
      · subst left'
        exact le_rfl
      · exact (Nat.pair_lt_pair_left right h).le
    _ ≤ Nat.pair left' right' := by
      rcases hright.eq_or_lt with h | h
      · subst right'
        exact le_rfl
      · exact (Nat.pair_lt_pair_right left' h).le

private theorem natBitLength_mono_local {left right : ℕ}
    (hle : left ≤ right) : natBitLength left ≤ natBitLength right :=
  Nat.add_le_add_right (Nat.log_mono_right hle) 1

/-- Switching the payload tag from true to false can only decrease the
constant-depth prefix-marker code. -/
theorem encodeNestedBalancedPrefixCNFPayloadMarker_le_flat
    (payload assignment count : ℕ) :
    encodeNestedBalancedPrefixCNFPayloadMarker payload assignment count ≤
      encodeBalancedPrefixCNFPayload payload assignment count := by
  simp only [encodeNestedBalancedPrefixCNFPayloadMarker,
    nestedBalancedPrefixCNFMarkerOfPayload,
    encodeBalancedPrefixCNFPayload, balancedPrefixCNFMarkerOfPayload,
    Encodable.encode_list_cons, Encodable.encode_list_nil,
    Encodable.encode_prod_val, Encodable.encode_true,
    Encodable.encode_false]
  apply Nat.succ_le_succ
  apply pair_mono (by rfl)
  apply Nat.succ_le_succ
  apply pair_mono
  · apply Nat.succ_le_succ
    apply pair_mono
    · exact pair_mono (by omega) (by rfl)
    · rfl
  · rfl

/-- Hence the already proved constant-depth flat-marker width formula also
bounds every nested-prefix query. -/
theorem encodeNestedBalancedPrefixCNFPayloadMarker_bits_le
    (payload assignment count : ℕ) :
    natBitLength
        (encodeNestedBalancedPrefixCNFPayloadMarker payload assignment count) ≤
      64 * max 1
        (max (natBitLength payload)
          (max (natBitLength assignment) (natBitLength count))) + 31 := by
  exact (natBitLength_mono_local
    (encodeNestedBalancedPrefixCNFPayloadMarker_le_flat payload assignment
      count)).trans
        (encodeBalancedPrefixCNFPayload_bits_le payload assignment count)

end NearCubicWires.NestedBalancedCNFCodec
