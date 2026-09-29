import Proof.MachineModel.BankAtomContextRegisters

/-!
# The projection-runner table, executed from the numeral bank's frame

`BankAtomContextRegisters.inverseAtomContextRuns_ofTable` leaves one residual,
`InverseAtomTableRuns`: from the numeral bank's frame produce

`encodeBalancedList (projectionRunnerCallOutputs pcp scheduledInput)`.

`ProjectionRunnerBalancedProgram.run_projectionRunnerBalancedProgram` already
executes that list — but from the runner's *own* request frame

`pair (queryCount * width + 2 ^ width) (pair (encodeBitInput input) (pair width
queryCount))`,

which mentions the scheduled refuter word, the scheduled width and the
scheduled query count.  Every one of those three is available from the bank
with no schedule immediate:

* the refuter word is `BankRefuterWordFrameProgram.run_bankRefuterWordFrameProgram`,
  whose only immediate is the machine description;
* `2 ^ width` is `CanonicalTwoPowProgram.run_binaryTwoPowProgram` on the width
  register;
* `queryCount * width` is `CanonicalBitSerialMulProgram.run_bitSerialMulProgram`
  on the two registers.

§2–§5 are the three straight-line frames that thread those four values into the
runner's request, §6 links the whole stage, and §7 discharges
`InverseAtomTableRuns` on the schedule's diagonal.

## The diagonal, again

The runner's run is stated at the *PCP input's* public length while the stage
runs at the request's public length, exactly as `BankFrameLoweringAdapter` §4
records.  §6 takes the identification as an equation between the two lengths
and §7 supplies it from the onset-restricted diagonal hypothesis the consumer
already threads.  Nothing is asserted.
-/

namespace NearCubicWires.BankProjectionTableStage

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerAtomProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

/-! ## 2. Frame duplication -/

/-! ## 3. The multiplier's request, read off the bank -/

/-! ## 4. The exponent's request, re-read off the frame -/

/-! ## 5. The runner's own request -/

/-! ## 6. The stage, linked -/

/-! ### Resource envelopes, one named function per stage -/

/-! ## 7. `InverseAtomTableRuns`, discharged on the diagonal -/

end NearCubicWires.BankProjectionTableStage
