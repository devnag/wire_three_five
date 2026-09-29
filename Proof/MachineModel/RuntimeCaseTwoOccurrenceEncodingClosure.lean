import Proof.MachineModel.RuntimeCaseTwoOccurrencePacketSplit
import Proof.MachineModel.RuntimeCaseTwoOracleTripleProgram

/-!
# The Case-2 occurrence residual, reduced to one numeral

`RuntimeCaseTwoOccurrencePacketSplit` cut the seven-numeral premise down to the
oracle triple: the published factory's clause width at the Case-2 substituted
circuit, that circuit's size, and its encoding.  `RuntimeCaseTwoOracleTripleProgram`
shows the first two are fixed-program functions of the third together with the
circuit's arity — and the arity is the schedule quad's second numeral, which §2
of the split module already emits.

So the whole oracle half collapses to the **single** encoder

> `InverseScheduledOccurrenceEncoding` — one fixed program that, from the
> requested public length alone, emits
> `encodeBooleanCircuit (caseTwoSubstitutedCircuit caseTwo)` at the oracle the
> branch carries.

§1 states it.  §2 assembles the arity stream beside it and re-proves the oracle
triple.  §3 restates the bank/diagonal cluster's three residuals at that single
premise.  This is the residue the prose of `RuntimeCaseTwoOccurrenceClosure`
predicted, now as a theorem rather than a remark.

## Where the register discipline goes

The arity is read from the published shape runner at the target's own public
length, which the schedule diagonal identifies with the scheduled source
length; the encoder is entered at the same length; and the assembled pair is
handed to the frozen triple stream through the ordinary
`CanonicalNativeCallProgram` frame inside it.  Both envelopes are branch reads
for the reason `BankCaseTwoEnvelopeClosure` records — the Case-2 oracle is
bound inside the premise — and here the *fuel* is a branch read too, since the
factory's own runner budgets are stated at the substituted circuit.
-/

namespace NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure

open NearCubicWires
open NearCubicWires.BankAtomContextRegisters
open NearCubicWires.BankCaseTwoEnvelopeClosure
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankFramedTargetChains
open NearCubicWires.BankProjectionTableStage
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankRegisterCaseTwoChain
open NearCubicWires.BankResidualClusterClosure
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.BankScheduledRowStageClosure
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoBlockOccurrenceProgram
open NearCubicWires.RuntimeCaseTwoOccurrenceClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoOracleTripleProgram
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The single encoder -/

/-! ## 2. The oracle triple from the encoder -/

/-! ## 3. What the cluster closure still needs -/

end NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
