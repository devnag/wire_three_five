import Proof.MachineModel.PreserveRightProgram
import Proof.MachineModel.TaggedProgramChoice

/-!
# Fixed heterogeneous projection-runner call

The structural recovery builder needs exactly two imported computations:
projection-address bits and verifier decision clauses.  This module gives them
one fixed tagged callee.  Each branch preserves its structural context beside
the imported result, so later node emission never reconstructs width, count,
or loop coordinates from an untyped host value.
-/

namespace NearCubicWires.ProjectionRunnerCallProgram

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

end NearCubicWires.ProjectionRunnerCallProgram
