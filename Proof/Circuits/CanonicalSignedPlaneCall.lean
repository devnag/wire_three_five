import Proof.Circuits.CanonicalBalancedCall
import Proof.Circuits.VerifiedPlaneRequestBuilder

/-!
# Width-safe signed-plane rectangular calls

The signed-plane printer makes a variable number of calls to the published
rectangular-product program.  This module fixes the production call ABI to the
canonical balanced list representation; neither requests nor outputs pass
through the legacy linked-list accumulator.
-/

namespace NearCubicWires.CanonicalSignedPlaneCall

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPrinter
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedPlaneRequestBuilder
open NearCubicWires.VerifiedLinker

@[simp] private theorem natCast_not_negative (magnitude : ℕ) :
    ¬(magnitude : ℤ) < 0 :=
  not_lt.mpr (Int.natCast_nonneg magnitude)

/-! ## One signed bit-plane call -/

/-! ## One raw request to one canonical balanced output -/

end NearCubicWires.CanonicalSignedPlaneCall
