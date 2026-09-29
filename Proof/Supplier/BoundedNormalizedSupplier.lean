import Proof.Circuits.ComponentwisePolynomial

/-!
# Supplier guarantees on normalization-produced circuits

The threshold-normalization source returns explicit parameter bounds.  Those
bounds are essential: a wire cap controls support incidence, but cannot bound
the exact-decomposition output of an arbitrarily large coefficient encoding.
This module records the single admissible supplier interface used by recovery;
it reuses the same estimator algorithms and only adds the normalization
certificate at the existing guarantee boundary.
-/

namespace NearCubicWires.BoundedNormalizedSupplier

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

end NearCubicWires.BoundedNormalizedSupplier

namespace NearCubicWires.ComponentwisePolynomial

open NearCubicWires
open NearCubicWires.BoundedNormalizedSupplier
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SupplierPipeline

end NearCubicWires.ComponentwisePolynomial
