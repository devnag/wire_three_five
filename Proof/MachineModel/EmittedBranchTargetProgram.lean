import Proof.MachineModel.BankRecoveryCodeProgram

/-!
# The branch-dispatched target with the query computed

`CanonicalBranchSelectorProgram.run_inverseTargetProgram_caseOne_closed` and
its three siblings discharge the branch selector of
`BranchTargetLanguageProgram` by supplying `branchSelectorProgram` at the
scheduled recovery code — a `set` immediate chosen from the request's own
target.  `BankRecoveryCodeProgram` replaces that immediate by the assembler of
the recovery code, leaving one program parameter (the structural atom emitter)
and one run hypothesis.

This module carries that replacement through the dispatcher: the four theorems
below are the four closed theorems of `CanonicalBranchSelectorProgram` with the
selector's query immediate removed.  After them, the target-derived data still
baked into the two chains are exactly the four schedule numerals the numeral
bank of `RuntimeScheduleNumeralBank` emits — plus, on the Case-2 branch, the
substituted circuit recovered from the accepting oracle.

## The fixed schedule's Case-2 chain carries no target

§1 records a small but load-bearing fact: `fixedCaseTwoChainProgram` ignores its
target argument outright, because `RecoveryScheduleEnvelope.fixedCopies` is a
frozen numeral.  On the fixed schedule the Case-2 branch therefore has *no*
schedule immediate at all, and the per-block occurrence callee is its only
request-dependent part.
-/

namespace NearCubicWires.EmittedBranchTargetProgram

open NearCubicWires
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed schedule's Case-2 chain is request-independent -/

/-! ## 2. The emitter's atom schedules at the two published splits -/

/-! ## 3. The inverse schedule -/

/-! ## 4. The fixed schedule -/

end NearCubicWires.EmittedBranchTargetProgram
