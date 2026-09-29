import Proof.MachineModel.RuntimeCaseTwoSubstitutedEncodingClosure

/-!
# The Case-2 request word's three numerals

`RuntimeCaseTwoSubstitutedEncodingClosure.InverseSubstitutionRequestWord` asks
for one program emitting

> `pair (encodeBooleanCircuit caseTwo.circuit)
>   (pair nativeWidth (pair sourceLength (encodeBitInput refuterWord)))`

from the requested public length.  Three of those four fields are already
published streams, and this module links them.

* The **native width** is `RuntimeScheduleQuadNumeralProgram.nativeWidthProgram`
  at the published shape runner, entered at the target's own public length; the
  schedule diagonal turns that length into the scheduled source length.
* The **scheduled source length** and the **refuter word** are the numeral
  bank's own registers: `UniformTargetLanguageBank.publishedBankProgram` emits
  the frame and `BankRefuterWordFrameProgram.bankRefuterWordFrameProgram`
  turns it into `pair (encodeBitInput word) (pair sourceLength pointCode)`, so
  one three-instruction adapter reshapes it into the pair the request word
  wants.  The diagonal is *threaded*, never asserted: it enters as the same
  hypothesis `RuntimeCaseTwoOccurrenceEncodingClosure` already carries.

§1 is the adapter, §2 the two bank numerals, §3 the frame, and §4 discharges
`InverseSubstitutionRequestWord` from one premise: a program emitting the
recovered oracle's *own* circuit code from the public length.  Nothing about
the substitution, the restriction, the arity padding or the three numerals is
left open.
-/

namespace NearCubicWires.RuntimeCaseTwoRequestWordFrame

open NearCubicWires
open NearCubicWires.BankRefuterWordFrameProgram
open NearCubicWires.BankRegisterCaseOneChain
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeCaseTwoOccurrenceEncodingClosure
open NearCubicWires.RuntimeCaseTwoOccurrencePacketSplit
open NearCubicWires.RuntimeCaseTwoSubstitutedEncodingClosure
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.RuntimeScheduleQuadNumeralProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The refuter-word adapter

Input the refuter frame `pair word (pair sourceLength pointCode)`, output the
request word's tail `pair sourceLength word`. -/

/-! ## 2. The two bank numerals -/

/-! ## 3. The three-numeral frame -/

/-! ## 4. The request word from the oracle's own code -/

end NearCubicWires.RuntimeCaseTwoRequestWordFrame
