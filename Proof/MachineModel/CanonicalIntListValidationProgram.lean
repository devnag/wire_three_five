import Proof.MachineModel.CanonicalBalancedValidationMapProgram
import Proof.MachineModel.CanonicalRationalValidationProgram

/-!
# Canonical integer-list validation

Integer atoms reuse the canonical-rational validator at denominator one.  This
keeps signed canonicality on the same executable path used by legal
coefficients; no second signed-integer parser is introduced.
-/

namespace NearCubicWires.CanonicalIntListValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedValidationMapProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.VerifiedLinker

/-! ## Fixed denominator-one lowering -/

/-! ## Direct rational-validator composition -/

/-! ## One balanced validation path -/

/-! ## Exact list semantics -/

end NearCubicWires.CanonicalIntListValidationProgram
