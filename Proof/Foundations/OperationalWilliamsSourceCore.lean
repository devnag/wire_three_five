import Proof.Foundations.LocalBitMultitapeCore
import Statement

/-!
# Cycle-free operational published source core

This lower layer contains exactly the finite local bit-machine semantics,
streamed Williams carrier, literal-receipt local Williams certificate,
canonical rule-table description, and faithful public contract needed by
`SourceContracts`.  It imports no supplier, recovery, or source-contract
consumer.  The semantic-only constructor from an arbitrary rectangular
algorithm intentionally remains in the higher diagnostic module.
-/

namespace NearCubicWires.WilliamsProductCertificate

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces


@[simp] theorem rowMajorNatMatrix_length {rows columns : ℕ}
    (matrix : NatMatrix rows columns) :
    (rowMajorNatMatrix matrix).length = rows * columns := by
  simp [rowMajorNatMatrix, List.length_flatten, List.sum_ofFn]

end NearCubicWires.WilliamsProductCertificate

namespace NearCubicWires.WilliamsLoaderForms

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.WilliamsProductCertificate

/-! ## 1. Canonical explicit-tape Williams source carrier -/




end NearCubicWires.WilliamsLoaderForms

namespace NearCubicWires.WilliamsPublishedForm

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LocalBitMultitape
open NearCubicWires.SourceInterfaces
open NearCubicWires.WilliamsProductCertificate
open NearCubicWires.WilliamsLoaderForms

/-! ## Canonical encoding of the exhibited finite rule table -/



/-! ## Corrected source field -/

/-! ## Safe projections -/

/-! ## Literal-receipt consequences used by downstream consumers -/


end NearCubicWires.WilliamsPublishedForm
