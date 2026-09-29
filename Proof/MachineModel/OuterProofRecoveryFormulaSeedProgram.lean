import Proof.MachineModel.BalancedClauseStreamFlattenProgram
import Proof.MachineModel.BitInputPrefixProgram
import Proof.MachineModel.CanonicalTwoPowProgram
import Proof.MachineModel.CircuitInputTautologyProgram
import Proof.MachineModel.TaggedProgramChoice
import Proof.MachineModel.RecoveredProofRequestCompilerProgram

namespace NearCubicWires.OuterProofRecoveryFormulaSeedProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CircuitInputCNF
open NearCubicWires.CircuitInputTautologyProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.VerifiedLinker

/-! ## 1. The chunk schedule of the recovery formula -/

/-! ## 2. The fixed chunk callee

The balanced range generator hands the callee `pair index context` at the
public length, with `context = pair width (encodeBitInput input)`.  Three fixed
adapters turn that into the tagged dispatcher's own ABI: the dispatch bit at
position `width` becomes the tag, and the low `width` bits become the shared
payload address. -/

/-! ### The zero-tag branch: one published input tautology -/

/-! ### The fixed chunk callee -/

/-! ## 3. The whole raw clause stream

One canonical balanced range, one canonical balanced call, and the canonical
clause-stream flattener turn the schedule parameters into the exact raw clause
stream of the C.12 recovery formula. -/

/-! ## 4. The seed frame

The seed request of `RecoveredProofRequestCompilerProgram` is the emitted
stream beside the proof-address count and the retained schedule frame.  Three
straight-line adapters and two applications of the published dyadic
exponential produce it; the scheduled width enters as the single immediate of
the instruction stream. -/

/-! ### The composed seed program -/

/-! ## 5. The scheduled instance

At the published schedule the emitted seed is literally
`RecoveredProofRequestCompilerProgram.recoveredProofCompilerSeedOutput`. -/

end NearCubicWires.OuterProofRecoveryFormulaSeedProgram
