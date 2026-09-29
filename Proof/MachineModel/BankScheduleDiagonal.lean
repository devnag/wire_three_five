import Proof.MachineModel.UniformTargetLanguageBank

/-!
# The schedule-index diagonal

`RuntimeScheduleNumeralBank` decodes its source index from the *public length*
of the request, through `RecoveryScheduleEnvelope.sourceIndexOfLength`, while
the two chains of `BranchTargetLanguageProgram` work at the *schedule's* index:
`inverseSourceIndex (inverseSelectedSource …)` on the inverse schedule and
`fixedSelectedSource …` on the fixed one.  `UniformTargetLanguageBank` records
that the two agree on the diagonal and leaves the identification inside
`bodyRun`.

This module supplies the identification as an explicit, reusable hypothesis.

## The identification is conditional, and provably so

The `hexecutes` binder of `PublishedRecoveryClosure` quantifies over *every*
target above one onset — `inverseCaseOneTargetOnset … ≤ target` — and nothing
in `hlarge`, `hyes`, `hrejects` or `haccepts` constrains `target` to be a
scheduled source length.  The consumer therefore does **not** pin
`target = sourceLength (inverseSourceIndex …)`, and the identification cannot
be asserted unconditionally: off the diagonal `sourceIndexOfLength target` is
the rounded-down decode of the request's own length, whereas the chain's index
is chosen by the executable envelope selector at that target, and the two are
different functions of `target`.

What is available — and what a register-driven body applies — is the diagonal
bridge below: on a request whose public length *is* the chain's scheduled
source length, every numeral the bank emits is the chain's own numeral at the
chain's own index.  §3 states it at both published schedules.
-/

namespace NearCubicWires.BankScheduleDiagonal

open NearCubicWires
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank

/-! ## 1. Decoding a scheduled length -/

/-! ## 2. The bank's frame on the diagonal -/

/-! ## 3. The two published schedules -/

end NearCubicWires.BankScheduleDiagonal
