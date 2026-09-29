import Proof.CaseAnalysis.CaseTwoCanonicalCircuitEncoder
import Proof.MachineModel.RuntimeCaseTwoRequestWordFrame

/-!
# The recovered oracle's own code, at the scheduled branch

`RuntimeCaseTwoRequestWordFrame.inverseSubstitutionRequestWord_ofCircuitEncoding`
cut the Case-2 request word down to `InverseScheduledCircuitEncoding`: one
program emitting `encodeBooleanCircuit caseTwo.circuit` from the public length.
`CaseTwoCanonicalCircuitEncoder.run_canonicalCircuitEncoderProgram` builds that
program out of the published prefix-SAT reducer and one *oracle-free* grouping
decoder, once its own request word

> `pair (generatedBalancedRangeInput descriptionWidth atomStream)
>   (pair nativeWidth sizeBound)`

is on the table.  This module links the two.

The request word above is exactly the frame-lowering stage that
`BankEmittedAtomLoop.InverseFrameAdapterRuns` already names on the selector
side — the coordinate count, the emitter's atom stream and two numerals, all
read from the schedule.  It enters here as one named premise with the same
shape, so the resulting statement is honest about what is still open: the
description frame and the grouping decoder, and nothing else.
-/

namespace NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure

open NearCubicWires
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoCanonicalCircuitEncoder
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoRequestWordFrame
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The description frame -/

/-! ## 2. The encoder at the schedule -/

/-! ## 3. The request word, from the same two premises -/

/-! ## 4. The bank cluster's encoder premise -/

end NearCubicWires.RuntimeCaseTwoCircuitEncodingClosure
