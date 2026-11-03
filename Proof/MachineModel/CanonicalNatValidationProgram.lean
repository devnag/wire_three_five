import Proof.MachineModel.CanonicalBalancedValidationProgram
import Proof.MachineModel.CanonicalNativeEqualityProgram
import Proof.MachineModel.CanonicalNatDecodeProgram
import Proof.MachineModel.PreserveRightProgram

/-!
# Total canonical-natural validation

The public natural codec is a canonical balanced list of little-endian bits.
This module gives arbitrary raw naturals one executable boundary: normalize
the traversed tree, fold its atoms to a native candidate, re-encode that
candidate with the canonical `encodeNat` instruction, and compare the result
with the untouched input.  Thus malformed tags, non-Boolean atoms, alternate
tree shapes, and high zeroes all follow the same rejection path.
-/

namespace NearCubicWires.CanonicalNatValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNatDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

def canonicalNatCandidate (raw : ℕ) : ℕ :=
  taggedBitFoldValue (rawBalancedTraversalTree raw).atoms 0 1

/-! ## Total raw-to-candidate pass -/

/-! ## Semantic canonicality -/

theorem canonicalNatCandidate_of_decode
    {raw value : ℕ} (hdecode : decodeNat raw = some value) :
    canonicalNatCandidate raw = value := by
  have hcode : encodeNat value = raw :=
    encodeNat_of_decode hdecode
  have hatoms :
      (rawBalancedTraversalTree raw).atoms =
        value.bits.map boolCode := by
    rw [← hcode]
    unfold encodeNat encodeBits encodeBoolList
    rw [← balancedTraversalTree_code]
    simp [RawBalancedTraversalTree.atoms,
      rawBalancedTraversalTree_normalized_code,
      balancedTraversalTree_atoms]
  rw [canonicalNatCandidate, hatoms,
    show value.bits.map boolCode = value.bits.map Bool.toNat by rfl,
    taggedBitFoldValue_boolBits, bitsValue_natBits]

def canonicalNatValidationOutput (raw : ℕ) : ℕ :=
  let candidate := canonicalNatCandidate raw
  if encodeNat candidate = raw then Nat.pair 1 candidate else 0

theorem canonicalNatValidationOutput_of_decode
    {raw value : ℕ} (hdecode : decodeNat raw = some value) :
    canonicalNatValidationOutput raw = Nat.pair 1 value := by
  have hcandidate := canonicalNatCandidate_of_decode hdecode
  have hcode := encodeNat_of_decode hdecode
  simp [canonicalNatValidationOutput, hcandidate, hcode]

@[simp] theorem canonicalNatValidationOutput_encodeNat (value : ℕ) :
    canonicalNatValidationOutput (encodeNat value) =
      Nat.pair 1 value :=
  canonicalNatValidationOutput_of_decode (decodeNat_encode value)

theorem canonicalNatValidationOutput_ne_zero_iff
    (raw : ℕ) :
    canonicalNatValidationOutput raw ≠ 0 ↔
      ∃ value, decodeNat raw = some value := by
  constructor
  · intro hnonzero
    by_cases hcanonical :
        encodeNat (canonicalNatCandidate raw) = raw
    · exact ⟨canonicalNatCandidate raw, by
        exact (congrArg decodeNat hcanonical.symm).trans
          (decodeNat_encode (canonicalNatCandidate raw))⟩
    · simp [canonicalNatValidationOutput, hcanonical] at hnonzero
  · rintro ⟨value, hdecode⟩
    rw [canonicalNatValidationOutput_of_decode hdecode]
    have hpositive : 0 < Nat.pair 1 value :=
      (show 0 < 1 by omega).trans_le (Nat.left_le_pair 1 value)
    exact hpositive.ne'

/-! ## Retain the untrusted word while computing its candidate -/

/-! ## Re-encode and retain the candidate through equality -/

/-! ## Collapse the equality flag to the public presence-tagged result -/

/-! ## Sole public total validator -/

end NearCubicWires.CanonicalNatValidationProgram
