import Proof.Circuits.CanonicalSignedPlaneCall
import Proof.MachineModel.CanonicalBooleanRangeAggregationProgram
import Proof.MachineModel.CanonicalFourfoldRowProgram

/-!
# One executable normalized-estimator pipeline

Both normalized circuit families use the same raw request envelope, aggregation
program, and canonical ratio packer.  This module fixes that composition and
its complete interpreter budget.  The accuracy exponent is compile-time data,
so the request carries neither a denominator function nor a denominator
certificate.  The aggregation artifact must compute canonical
numerator/denominator components from the typed envelope; no field may provide
a final rational code or an alternate semantic estimate.
-/

namespace NearCubicWires.SharedNormalizedEstimatorProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBooleanRangeAggregationProgram
open NearCubicWires.CanonicalFourfoldRowProgram
open NearCubicWires.CanonicalSignedPlaneCall
open NearCubicWires.CanonicalSupplierSupportCompressionProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.WilliamsPublishedForm
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.VerifiedLinker
open NearCubicWires.VerifiedPlaneRequestBuilder

/-! ## Canonical aggregation-component handoff -/

/-! ## One row-major semantic bridge -/

/-- Low-to-high input codes form the exact finite enumeration used by the
fixed row ABI.  Keeping this equivalence beside the aggregation controller
prevents an unverified bit-order conversion at the final count. -/
def fourfoldInputFinEquiv (q : ℕ) : BitInput q ≃ Fin (2 ^ q) where
  toFun input := ⟨encodeBitInput input, by
    rw [encodeBitInput_eq_ofBits]
    exact Nat.ofBits_lt_two_pow input⟩
  invFun code := rowBitInputOfCode q code.val
  left_inv := rowBitInputOfCode_encode
  right_inv code := by
    apply Fin.ext
    exact encodeBitInput_testBit code.isLt

/-! ## The one remaining concrete aggregation artifact -/

/-! ## Canonical executable dependencies from the published contracts -/

/-! ## Closed linker and `SharedNormalizedEstimator` constructor -/

end NearCubicWires.SharedNormalizedEstimatorProgram
