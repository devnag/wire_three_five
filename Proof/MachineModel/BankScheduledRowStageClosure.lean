import Proof.MachineModel.BankRegisterCaseOneChain

/-!
# The Case-1 chain's row residual, discharged

`BankRegisterCaseOneChain` left exactly one premise, `InverseScheduledRowRuns`:
one decision-row stage that, at the schedule's own source index and public
length, emits the padded decision row of every requested randomness code.
`OuterProofRowStageProgram.outerProofRowScheduledProgram` is now such a stage
*uniformly in the target*, so the premise is discharged by quoting its run.

## Why the stage is target uniform

The row stage used to carry two immediates, the scheduled native width and the
scheduled query count, both chosen from the requested target.  Neither is
recoverable from the row's input frame: the `width` that frame carries is
`RecoveryScheduleEnvelope.scheduledWidth`, i.e. the *envelope*
`ProjectionWidthEnvelope.widthEnvelope`, which `nativeWidth_le_widthEnvelope`
bounds the native width by but does not equal it.

Both numerals are, however, the two components of one published object:
`ExecutableProjectionPCP.nativeWidth` and `ExecutableProjectionPCP.queryCount`
are the left and right halves of `ExecutableProjectionPCP.shapeCode`, and that
code is produced by the published shape runner `pcp.shape` from the public
length alone.  `VerifiedLinker.linkPrograms` preserves register one — the
public length — through every stage, so each stage of the row that needs a
numeral reloads the length, runs the published shape program and unpairs.  No
frame above the row changes shape, and no numeral remains an immediate.

## What is left

Only the scheduled query-count positivity, which
`BranchTargetLanguageProgram` already documents as unavailable from the
published interface — `ExecutableProjectionPCPGuarantee` bounds `queryCount`
from above only — and therefore carries as an explicit hypothesis on the
Case-1 branch.  It is carried here in exactly the same way.
-/

namespace NearCubicWires.BankScheduledRowStageClosure

open NearCubicWires
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRowStageProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. The scheduled row stage and its envelopes -/

/-! ## 2. The scheduled query-count side condition -/

/-! ## 3. `InverseScheduledRowRuns`, discharged -/

end NearCubicWires.BankScheduledRowStageClosure
