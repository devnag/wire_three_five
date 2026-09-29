import Proof.MachineModel.CanonicalBalancedValidationProgram

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

/-! ## Total raw-to-candidate pass -/

/-! ## Semantic canonicality -/

/-! ## Retain the untrusted word while computing its candidate -/

/-! ## Re-encode and retain the candidate through equality -/

/-! ## Collapse the equality flag to the public presence-tagged result -/

/-! ## Sole public total validator -/

end NearCubicWires.CanonicalNatValidationProgram
