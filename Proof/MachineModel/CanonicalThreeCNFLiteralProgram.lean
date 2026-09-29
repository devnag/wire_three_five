import Proof.MachineModel.CanonicalEncodedListLookupProgram
import Proof.MachineModel.CanonicalLiteralDecodeProgram

/-!
# Fixed pointwise `ThreeCNF` literal decoder

This is the complete codec boundary for one decision-runner literal.  The first
fixed callee traverses the outer clause spine and inner literal spine; the
second fixed callee applies the exact public literal decoder.  Arity is carried
through the first stage with the shared preserving adapter, so no host decode
or duplicate list cursor appears between the two interpreters.
-/

namespace NearCubicWires.CanonicalThreeCNFLiteralProgram

open NearCubicWires
open NearCubicWires.CanonicalEncodedListLookupProgram
open NearCubicWires.CanonicalLiteralDecodeProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

end NearCubicWires.CanonicalThreeCNFLiteralProgram
