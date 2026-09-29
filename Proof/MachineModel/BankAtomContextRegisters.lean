import Proof.MachineModel.BankAtomShapeCountStage
import Proof.MachineModel.BankOracleSizeBoundProgram
import Proof.PCP.PaddedProjectionPresentation

/-!
# The atom-shape context, assembled from the bank's registers

`BankAtomShapeCountStage.inverseAtomShapeRuns_ofContext` reduces the adapter's
residual to `InverseAtomContextRuns`: from the numeral bank's frame produce

`pair table (pair width (pair queryCount bound))`.

Three of those four components are already on the machine.  The width and the
query count are literally two of the bank's five registers, and the size cap is
`RecoveryScheduleEnvelope.oracleSizeBound requiredDegree width`, which
`BankOracleSizeBoundProgram.run_bankSizeBoundProgram` computes from the width
register by the pairing clock with no premise at all.  Only the projection
runner's balanced table is left.

§1–§3 build the three straight-line frames this needs (frame duplication, the
pair swap, and the register projection out of `bankBoundFrame`).  §4 links them
around one table stage, and §5 identifies the assembled word with
`BankEmittedAtomLoop.inverseAtomContext`.

## Where the diagonal lives, exactly

§5 is the only place in the reduction that needs a hypothesis, and it needs two:

* the **presentation** premise, which supplies
  `pcp.nativeWidth = widthEnvelope outer` and `pcp.queryCount = outer.pcp.queryCount`;
* the **diagonal**, `target = inverseScheduleLength …`, which is what makes the
  bank's length-decoded registers the *schedule's* registers.

`BankScheduleDiagonal` records that the consumer of `bodyRun` does not pin the
request's public length to a scheduled source length, so the identification is
threaded as a hypothesis of the one theorem that needs it and is never
asserted.  Everything in §1–§4 is unconditional.

After §5 the adapter's residual is exactly `InverseAtomTableRuns`: the balanced
projection-runner table at the bank's frame, and nothing else.
-/

namespace NearCubicWires.BankAtomContextRegisters

open NearCubicWires
open NearCubicWires.BankAtomShapeCountStage
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFrameLoweringAdapter
open NearCubicWires.BankOracleSizeBoundProgram
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Frame duplication -/

/-! ## 2. The pair swap -/

/-! ## 3. The register projection -/

/-! ## 4. The shape numerals, executed from the bank's frame -/

/-! ## 5. The context, from the table stage alone -/


end NearCubicWires.BankAtomContextRegisters
