import Proof.Foundations.SupplierPipeline

/-!
# Executable Fourfold request envelope

The supplier VM receives a canonical `FourfoldRequest.code` in register zero
and the request arity in register one.  This fixed oracle-free stage strips the
three structural list cells and emits a compact handoff containing the encoded
family tag, numeric arity, and raw circuit-list code.  Circuit decoding and row
construction remain later linked stages; this module proves only the exact raw
ABI boundary and does not introduce a semantic parser callback.
-/

namespace NearCubicWires.FourfoldRequestEnvelopeProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.SupplierPipeline

end NearCubicWires.FourfoldRequestEnvelopeProgram
