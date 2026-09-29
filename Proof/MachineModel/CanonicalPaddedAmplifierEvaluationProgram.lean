import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalNativeCallProgram

/-!
# Canonical padded amplifier evaluation

The published amplifier evaluator is defined at its exact output arity, whereas
the final language is padded to a larger public arity.  This module supplies the
single executable adapter: truncate the public input with
`bitInputPrefixProgram`, retain the descriptor, and make one native-input call
to the published evaluator.  No high input bit or host-built evaluator request
crosses the call boundary.
-/

namespace NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.VerifiedLinker

end NearCubicWires.CanonicalPaddedAmplifierEvaluationProgram
