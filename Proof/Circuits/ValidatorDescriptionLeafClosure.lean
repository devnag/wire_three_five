import Proof.Circuits.ValidatorResidualLeafBudget

namespace NearCubicWires.ValidatorDescriptionLeafClosure

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.CanonicalBalancedBuilder
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalNormalizedCircuitDescriptionProgram
open NearCubicWires.CanonicalNormalizedCircuitResourceProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorLeafFuelBounds
open NearCubicWires.ValidatorLeafWidthCore
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.ValidatorStageEnvelopes
open NearCubicWires.VerifiedLinker

/-! ## §1 The unit-budget idiom

`PolyBounded value width budget k` unfolds to `value ≤ budget * (width + 1) ^ k`.
Read with `width` in the *measure* slot this is a purely local statement about a
charge and the width of the code it runs on — no request, no measure, no
polynomial envelope — and every rule of the domination algebra is available for
it.  §§2–5 are written entirely in that reading, and the two lemmas below are
the only places where it meets the real measure. -/

/-! ### The canonicality guard's closed unit budget

`ValidatorLeafFuelBounds` §5 dominates the guard with an explicit coefficient;
§6 states the *degree* result existentially, because a numeral there would
evaluate the canonicalization pipeline's register spans.  Naming the coefficient
expression as a `def` and instantiating it at the unit anchor gives the same
information without any evaluation. -/

/-! ## §4 One normalized gate's description

A gate summary carries its threshold as a signed code and its selected weights
as a signed-code list, and the description stage re-encodes what it decodes.
The re-encoding is either the original code — the decoders are canonical — or,
on a rejected code, the closed numeral `0`; either way it is no wider than the
code.  That is the whole width argument, and it is what lets the two stages be
charged against the *summary's* width alone. -/

/-! ### The gate's two stages -/

/-! ### The bottom-gate counted map and sum

The second counted combinator on the path.  Its callee is the gate description
above — degree `2` — and the count is the decoded summary list's, so the map
lands at degree `3`.  With the guard at `2` and the anchor at `1` that is the
map's own degree, and it is the last degree this module spends: everything above
is a linker, a wrapper, a native call at a singleton, or a family choice. -/

/-! ### The two family branches -/

end NearCubicWires.ValidatorDescriptionLeafClosure
