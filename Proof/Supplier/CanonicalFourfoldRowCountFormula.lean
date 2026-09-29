import Proof.MachineModel.CanonicalFourfoldRowTailProgram

/-!
# The published row counts as closed natural-number arithmetic

The row-major atom count consumed by the aggregation front end is
`rows.rowCount request * 2 ^ request.q`, and
`CanonicalFourfoldRowCountProgram` already executes the second factor and the
product.  The first factor is a `Fintype.card` of a dependent walk-sample
type, which no machine can evaluate directly.

This module removes that obstacle *before* any counting program is written:
it replaces both published row counts by explicit natural-number arithmetic in
the request's own data.  Nothing here is executable and nothing here is
asymptotic; every equality is an exact cardinality identity.

After this reduction the counting residual is purely numeric — a base-two
ceiling logarithm, the occurrence population, the touching cost, and (in the
threshold family) the prime-window cardinality.
-/

namespace NearCubicWires.CanonicalFourfoldRowCountFormula

open NearCubicWires
open NearCubicWires.FixedAccuracyDenominatorProgram
open NearCubicWires.SharedNormalizedEstimatorProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime
open NearCubicWires.SupplierTouching
open NearCubicWires.SupplierWalk
open NearCubicWires.SupplierWalkBridge

/-! ## §1 The canonical walk-sample cardinality -/

/-! ## §2 The two published row counts -/

/-! ## §3 Collapsing both factors to one dyadic exponent

The powered Margulis label alphabet has size `16 ^ 40 = 2 ^ 160`, so the whole
symmetric row count is a *single* power of two.  This is the shape an
executable counter can reach with one dyadic exponential: the residual becomes
an exponent, not a cardinality. -/

/-! ## §4 The two published atom counts -/

end NearCubicWires.CanonicalFourfoldRowCountFormula
