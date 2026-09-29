import Proof.MachineModel.CanonicalRationalValidationProgram

/-!
# Canonical legal-term validation

A legal circuit term is the fixed tagged tuple
`[canonical rational coefficient, family-specific circuit]`.  This module
validates that common prefix once and exposes the circuit code only after the
tuple and coefficient have both passed.  The mode-specific circuit validator
therefore has one fail-closed attachment point and never receives a
host-prepared payload.
-/

namespace NearCubicWires.CanonicalLegalTermValidationProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRationalValidationProgram
open NearCubicWires.CanonicalTaggedTupleProgram
open NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Fixed term tuple -/

/-! ## Tuple-field projection -/

/-! ## Rational validation with retained circuit context -/

/-! ## Fail-closed circuit handoff -/

/-! ## Unique composed coefficient prefix -/

end NearCubicWires.CanonicalLegalTermValidationProgram
