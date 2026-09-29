import Proof.MachineModel.CanonicalBooleanizeProgram
import Proof.Circuits.CanonicalPairedCall
import Proof.MachineModel.CanonicalSupplierSupportCompressionProgram

/-!
# Canonical Boolean range aggregation

This module closes the generic controller tail used by supplier rows.  A
single statically selected callee is applied to the canonical requests
`0, ..., count - 1`; the balanced output tree is reduced in place to its true
leaf count while an opaque denominator context is preserved.  The callee is a
link-time program parameter, never a run-time callback, and the public machine
has no flat-list or full-cube fallback.
-/

namespace NearCubicWires.CanonicalBooleanRangeAggregationProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanizeProgram
open NearCubicWires.CanonicalPairedCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

/-! ## Canonical component packing -/

/-! ## Closed aggregation-component program -/

/-! ## Signed-row Booleanization boundary -/

/-! ## Smallest pre-contraction witness -/

end NearCubicWires.CanonicalBooleanRangeAggregationProgram
