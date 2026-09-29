import Proof.PCP.PaddedProjectionShapeRunner

/-!
# The padded decision runner

The padded verifier's decision is the source verifier's decision on the
*native prefix* of the padded random string: the padding coordinates are never
read.  On canonical codes that is one modular reduction,

`encodeBitInput (prefixBits hwidth randomness) =
  encodeBitInput randomness % 2 ^ nativeWidth`,

which is `BitInputPrefixProgram.bitInputPrefix_encodeBitInput`; the reduction
itself is the published `bitInputPrefixProgram`, so no new bit loop is written.

The stream therefore has four stages: read the native width out of the
published shape runner's output, reduce the padded random code modulo that
width, rebuild the source decision runner's own request code, and delegate.
§2 packages the delegation as one reusable callee lemma so that the source
runner's `halts` field is consumed exactly once.
-/

namespace NearCubicWires.PaddedProjectionDecisionRunner

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The two straight-line framing streams -/

/-! ## 2. The one delegation lemma -/

/-! ## 3. The padded decision runner -/

/-! ## 4. The published instance -/

end NearCubicWires.PaddedProjectionDecisionRunner
