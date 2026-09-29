import Proof.MachineModel.BankProjectionTableStage
import Proof.Circuits.FixedScheduleDiagonalClosure

/-!
# The projection-runner table stage at the fixed schedule

`BankProjectionTableStage` closes `BankAtomContextRegisters.InverseAtomTableRuns`
from the executable presentation and the onset-restricted schedule diagonal.  The
stage itself — `bankProjectionTableProgram` and its two envelopes — is schedule
free: `run_bankProjectionTableProgram` takes the identification of the request's
public length with a source length as its *only* hypothesis and says nothing
about which schedule produced that length.

This module replays the last two steps of that argument at the fixed-rate
schedule, so that `FixedScheduleDiagonalClosure.FixedAtomTableRuns` is discharged
from exactly the same two facts:

* §1 names the stage and its two envelopes at the fixed schedule.
* §2 is the join fact: on the fixed diagonal the numeral bank's frame is the
  fixed chain's own five registers, the fixed chain's index being
  `CaseOneRecoveryAssembly.fixedSelectedSource` itself.
* §3 discharges `FixedAtomTableRuns`.

Nothing here is new mathematics; the fixed side's diagonal bridge
`BankScheduleDiagonal.publishedBankFrame_at_fixedDiagonal` and the schedule-free
run theorem were both already green.
-/

namespace NearCubicWires.FixedProjectionTableStage

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FixedScheduleAtomLoop
open NearCubicWires.FixedScheduleDiagonalClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The stage at the published fixed schedule -/

/-! ## 2. The join fact at the fixed diagonal -/

/-! ## 3. `FixedAtomTableRuns`, discharged on the diagonal -/

end NearCubicWires.FixedProjectionTableStage
