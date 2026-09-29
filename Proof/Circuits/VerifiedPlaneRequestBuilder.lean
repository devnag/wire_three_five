import Proof.Foundations.SupplierPrinter

/-!
# Canonical signed-plane request syntax

Signed-plane batches are machine input, so every variable-length component is
midpoint-balanced.  The old implementation first materialized linked token
streams and then bounded them by repeated self-pairing; both choices made the
claimed register envelope exponential in the number of entries.  The sole
production syntax below instead expands the deterministic bit/sign schedule
into balanced call atoms.  It duplicates only source data and public indices,
never a bit plane, product, score, or semantic answer.
-/

namespace NearCubicWires.VerifiedPlaneRequestBuilder

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPrinter

/-! ## Width-safe row-major source data -/

/-! ## Semantic rectangular requests, in exactly the executable order -/

end NearCubicWires.VerifiedPlaneRequestBuilder
