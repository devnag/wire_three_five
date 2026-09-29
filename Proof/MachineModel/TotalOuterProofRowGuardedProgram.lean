import Proof.MachineModel.OuterProofRowStageProgram
import Proof.Circuits.TotalRowCountGuard

/-!
# The total outer-proof row stream

`rowSeedProgram` emits `pair tableCode (pair queryCount decisionCode)`.  This
module replaces only the following `rowStreamProgram` call by
`TotalRowCountGuard.countGuardProgram rowStreamProgram`.  The zero branch emits
the canonical empty-row code; the nonzero branch reuses the existing stream
execution unchanged.
-/

namespace NearCubicWires.TotalOuterProofRowGuardedProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.OuterProofRowStageProgram
open NearCubicWires.SourceInterfaces
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.TotalRowCountGuard
open NearCubicWires.VerifiedLinker

/-! ## 2. Hostile zero and positive-count compatibility -/


end NearCubicWires.TotalOuterProofRowGuardedProgram
