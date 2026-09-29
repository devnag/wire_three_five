import Proof.MachineModel.FourfoldRequestEnvelopeProgram

/-!
# Canonical aggregation-envelope lowering

The public envelope stores its published family tag as a canonical natural.
This fixed adapter lowers the two typed public variants to the internal
right-associated context

`pair(mode, pair(q, balancedCircuitTree))`.

At this boundary the input has already been typed by `PublishedContracts`.
Consequently zero selects the symmetric family and nonzero selects threshold;
the public theorems below prove the exact canonical encodings of tags zero and
one take those paths.  Keeping validation at the typed boundary avoids a second
wire decoder and a shadow notion of envelope validity.
-/

namespace NearCubicWires.CanonicalAggregationEnvelopeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FourfoldRequestEnvelopeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline

end NearCubicWires.CanonicalAggregationEnvelopeProgram
