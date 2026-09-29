import Proof.Circuits.CanonicalBalancedCall
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.MachineModel.CanonicalRationalValidationProgram

/-!
# Exact rational coefficient-mass accounting

Canonical rational validation exposes one summary
`pair 1 (pair sign (pair magnitude denominator))`.  Coefficient mass ignores
the sign, so this module folds the exact nonnegative fractions without
rounding.  The accumulator deliberately need not be reduced: cross
multiplication preserves its value and avoids a second normalization path.
-/

namespace NearCubicWires.CanonicalRationalMassProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryArithmeticProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.CallableRelocation
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## One exact accumulator update -/

/-! ## Unique balanced accumulator controller -/

/-! ## Exact canonical-rational semantics -/

end NearCubicWires.CanonicalRationalMassProgram
