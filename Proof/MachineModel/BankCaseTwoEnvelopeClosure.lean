import Proof.MachineModel.BankResidualClusterClosure
import Proof.MachineModel.BankScheduledRowStageClosure

/-!
# The Case-2 bank envelopes, discharged

`BankRegisterCaseTwoChain` left two residuals.  This module discharges the
resource one, `InverseCaseTwoBankEnvelopes`, for *every* per-block occurrence
callee and both of its envelopes, and records what the cluster closure of
`BankResidualClusterClosure` then still needs.

## The binding hazard

The Case-2 body's own width and fuel are functions of the recovered accepting
oracle `caseTwo`, and `caseTwo` is bound *inside* `InverseCaseTwoBankEnvelopes`
— it is introduced by the branch equation, not by the request.  So neither
envelope can be written as an expression in the request alone by simply naming
the Case-2 body's cost.

It can be written as a *branch read*.  `CaseOneRecoveryAssembly.inverseTargetBranch`
is a total function of the request and one acceptance proof, and
`ScheduledRecovery.ScheduledOuterBranch` is a two-constructor inductive, so a
public `LanguageEvaluationRequest → ℕ` may decide acceptance classically, match
on the branch, and quote the Case-2 body's cost at whichever oracle the branch
itself carries.  Proof irrelevance makes the acceptance proof in the definition
the very proof the premise supplies, and constructor injectivity makes the
matched oracle the very oracle the premise supplies, so the domination the
premise asks for holds as an *equality* — no slack, no new bound.

That is `§1`; `§2` discharges the premise, and `§3` records the cluster's
remaining obligations.

## What `InverseScheduledOccurrenceRuns` still needs

`CaseTwoBlockOccurrenceProgram.caseTwoScheduledOccurrenceProgram` is the callee
at the scheduled coordinates, and its stream carries seven immediates.  Four
are schedule numerals and are removable by the register discipline
`OuterProofRowStageProgram` now uses — reload the public length from register
one and run a published runner:

* `outer.pcp.nativeWidth (sourceLength sourceIndex)` — the shape runner's left
  component, exactly as in `OuterProofRowStageProgram`;
* `ProjectionWidthEnvelope.widthEnvelope outer (sourceLength sourceIndex)` —
  `RuntimeScheduleNumeralBank.widthEnvelopeProgram`;
* `clauseBitsEnvelope outer pcppSource _ (sourceLength sourceIndex)` and
* `seedArity outer pcppSource requiredDegree sourceIndex`.

Three are *oracle* numerals and are not removable that way:

* `(caseTwoSubstitutedCircuit caseTwo).size`,
* `encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)`,
* `(caseTwoFactoryPCPP pcppSource caseTwo).clauseBits`.

`CanonicalTargetLanguageProgram.caseTwoSubstitutedCircuit` is
`outer.pcppCircuit input (restrictPaddedOracle caseTwo.circuit _)`, i.e.
`(outer.substitution.circuit ⟨_, input, oracle⟩).padToArity`.  The published
interface *does* execute the outer half of that:
`ExecutableInterfaces.ExecutableProjectionSubstitution.computes` runs
`outer.substitution.runner.program` and returns
`encodeBooleanCircuit (circuit request)` — but its request already contains the
oracle.  The oracle itself is what
`BoundedOracleRecoveryProgram` recovers, one description coordinate at a time
by SAT self-reduction; no module in the tree assembles those coordinates into
`encodeBooleanCircuit (restrictPaddedOracle caseTwo.circuit _)`, and none
executes `padToArity` or `restrictPaddedOracle`.

So the occurrence residual is one encoder (recovered description bits to a
padded, restricted circuit encoding) plus an internals pass over
`CaseTwoBlockOccurrenceProgram` turning its seven immediates into frame reads.
Neither is attempted here.
-/

namespace NearCubicWires.BankCaseTwoEnvelopeClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankCaseTwoSeedBlockListProgram
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BankResidualClusterClosure
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The Case-2 body's cost, read off the branch -/

/-! ## 2. `InverseCaseTwoBankEnvelopes`, discharged -/

/-! ## 3. What the cluster closure still needs -/

end NearCubicWires.BankCaseTwoEnvelopeClosure
