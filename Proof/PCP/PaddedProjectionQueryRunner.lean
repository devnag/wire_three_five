import Proof.PCP.PaddedProjectionDecisionRunner

/-!
# The padded query runner

The padded query runner cannot forward the source runner's answer verbatim.
`ExecutableInterfaces.decodeProjectedRandomBit` reduces the returned index
*modulo the width it is applied at*, so a native code read at the padded width
names a different address.  `PaddedProjectionRunnerOutputs.paddedQueryOutput`
therefore re-tags: the emitted index is the native index reduced modulo a
tag-dependent modulus — the native width on an address tag, two on a constant
tag — which the padded decode then reproduces exactly.

Two facts shape the stream.

* The source query runner is only obliged to halt on its *own* requests, so
  the padded runner must not call it outside the published shape.  The guard is
  the saturating product `(queryCount - query) * (nativeWidth - bit)`, which
  vanishes exactly off that shape; `TaggedProgramChoice.taggedProgramChoice`
  dispatches on it, and the vanishing branch emits the canonical false
  constant.

* Only one modular reduction is needed per side because the modulus itself is
  selected by a second `taggedProgramChoice` on the saturating difference
  `2 - tag`.  Every framing stream in this module is therefore straight-line;
  no instruction trace in the file contains a branch.
-/

namespace NearCubicWires.PaddedProjectionQueryRunner

open NearCubicWires
open NearCubicWires.CanonicalBitSerialModProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeModProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## 1. Two reusable dispatch wrappers -/

/-! ## 2. The straight-line framing streams -/

/-! ## 3. The in-range chain -/

/-! ## 4. The padded query runner -/

/-! ## 5. The published instance -/

end NearCubicWires.PaddedProjectionQueryRunner
