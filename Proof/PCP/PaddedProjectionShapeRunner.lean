import Proof.PCP.PaddedProjectionRunnerAssembly

/-!
# The padded shape runner

The first of the three runners `PaddedProjectionRunnerAssembly` asks for: one
fixed instruction stream emitting

`Nat.pair (widthEnvelope outer n) (outer.pcp.queryCount n)`

from the public length alone.  Neither component is recomputed here.  The
width envelope is `RuntimeScheduleNumeralBank.widthEnvelopeProgram`, whose
floor logarithm is already derived from the published ceiling-logarithm loop;
the query count is read at run time out of the published shape runner's own
output, so the padded runner bakes no shape numeral as an immediate.

Only two framing streams are new, and both are straight-line: one self-pairing
duplicator and one four-register reframer.  Everything else is
`PreserveRightProgram.preserveRightProgram` and one verified link per stage.
-/

namespace NearCubicWires.PaddedProjectionShapeRunner

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The two straight-line framing streams -/

/-! ## 2. The padded shape runner -/

/-! ## 3. The published instance -/

end NearCubicWires.PaddedProjectionShapeRunner
