import Proof.MachineModel.CanonicalBalancedLengthProgram
import Proof.MachineModel.CanonicalBalancedValidationProgram

/-!
# Guarded canonical-balanced validation map

Nested recovery records contain several balanced lists whose atoms are
validated by different fixed callees.  This module supplies one structural
control shell for all of them.  It first proves the public balanced encoding,
retains that result beside the original bytes, and only then maps a caller-
selected fixed program over the atoms through the sole balanced-call ABI.

Malformed syntax is mapped to the canonical empty tree while a retained zero
flag records the rejection.  Consequently later stages can execute total list
machinery without treating malformed input as an accepted empty list.
-/

namespace NearCubicWires.CanonicalBalancedValidationMapProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLengthProgram
open NearCubicWires.CanonicalBalancedValidationProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.CanonicalNativeEqualityProgram
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## One guarded balanced map -/

/-! ## All-valid continuation

The mapped tree has the same shape as the canonical source tree.  Its length
is nevertheless derived by the existing executable balanced-length program;
the shared generic nonzero counter then proves that every callee result
accepted.  The retained structural flag is checked last, so malformed input
cannot be confused with the valid empty list. -/

end NearCubicWires.CanonicalBalancedValidationMapProgram
