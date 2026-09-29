import Proof.CaseAnalysis.CaseTwoSubstitutedCircuitEncoder
import Proof.MachineModel.RuntimeCaseTwoOccurrenceEncodingClosure

/-!
# The Case-2 encoder, reduced to the recovered oracle's own code

`RuntimeCaseTwoOccurrenceEncodingClosure` cut the bank/diagonal cluster down to
`InverseScheduledOccurrenceEncoding`: one fixed program emitting
`encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)` from the public
length.  `CaseTwoSubstitutedCircuitEncoder` builds that encoder out of the
recovered oracle's *own* code together with three numerals that the bank
already emits — the native width, the scheduled source length and the refuter
word — so nothing of the substitution, the restriction or the arity padding is
left open.

§1 states the smaller premise: one program emitting the request word

> `pair (encodeBooleanCircuit caseTwo.circuit)
>   (pair nativeWidth (pair sourceLength (encodeBitInput refuterWord)))`

from the public length.  §2 links the substituted-circuit encoder onto it and
discharges `InverseScheduledOccurrenceEncoding` outright, so
`RuntimeCaseTwoOccurrenceEncodingClosure.inverse_clusterResiduals_ofEncoding`
applies with the assembler as the only constructive residue left in the bank
cluster.
-/

namespace NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure

open NearCubicWires
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoSubstitutedCircuitEncoder
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedOracleRestriction
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The request word -/

/-! ## 2. The encoder from the request word -/

end NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
