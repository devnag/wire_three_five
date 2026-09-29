import Proof.MachineModel.CaseTwoBlockOccurrenceProgram

/-!
# The executable Case-1/Case-2 branch selector

`BranchTargetLanguageProgram` links two closed chains onto the fixed tag
dispatcher and leaves the tag itself as a parameter: one program returning
`pair tag pointCode`, with `tag ≠ 0` exactly when the scheduled outer split
lands in Case 2.  This module builds that program.

The whole discrimination is one `sat` opcode.
`CanonicalTargetLanguageProgram.scheduledCaseTwo_iff_encodedSat` proves that
the encoded satisfiability of the canonical bounded-oracle recovery formula of
the scheduled refuter word is equivalent to the existence of a canonical
accepting oracle, which is precisely the branch condition of
`ScheduledRecovery.scheduledOuterBranch`.  The selector therefore consists of
one `copy`, one `set` of the recovery code, one `sat`, and one `pair`: no
circuit, oracle, or branch witness is supplied from outside, and no second
decision procedure is introduced.

Both directions are then instantiated:

* a `ScheduledCaseOneData` — the Case-1 payload of the canonical split, whose
  single field is the literal non-existence of a small accepting oracle —
  forces the tag to zero;
* a `CanonicalAcceptingOracle` forces the tag to one.

Composing with `CaseTwoBlockOccurrenceProgram`, §4 states the branch-dispatched
canonical target at both published schedules with the selector and the
per-block occurrence callee both discharged.  On the Case-1 branch the
scheduled query-count positivity of `OuterProofRowStageProgram` remains the one
side condition, exactly as `BranchTargetLanguageProgram` records.
-/

namespace NearCubicWires.CanonicalBranchSelectorProgram

open NearCubicWires
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoBlockOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryPipeline
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. One SAT query, then the tagged request

Register ABI: `r2` the retained point code, `r3` the recovery code, `r4` the
decided tag. -/

/-! ## 2. The scheduled recovery code and its two branch values -/

/-! ## 3. The selector at both published schedules -/

/-! ## 4. The branch-dispatched canonical target, selector discharged -/

end NearCubicWires.CanonicalBranchSelectorProgram
