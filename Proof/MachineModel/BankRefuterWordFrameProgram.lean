import Proof.MachineModel.RuntimeScheduleNumeralBank

/-!
# The refuter-word frame, read from the numeral bank

`RefuterWordFrameProgram.refuterWordFrameProgram` builds the frame

`pair (encodeBitInput word) (pair sourceLength pointCode)`

that every scheduled recovery stage consumes, but it takes the scheduled source
length as an *immediate* of its request prelude, so its instruction stream
depends on the request.  This module rebuilds exactly that frame from the
numeral bank's output instead: the scheduled source length is read out of a
register, and the only immediate left is
`ExecutableWeakNondeterministicMachine.description`, which the machine-dependence
analysis of `ExecutableTargetLanguagePackaging` already licenses as frozen.

Only the request prelude and the reframing adapter are rebuilt; the published
refuter call and the canonical low-bit normalizer are reused verbatim through
`CanonicalNativeCallProgram.nativeContextCallProgram` and
`BitInputPrefixProgram.bitInputPrefixProgram`, and the identification of the
truncated output code with the refuter's own word is
`RefuterWordFrameProgram.encodeBitInput_refuterOutput`.

This is the first of the four immediates listed at the packaging seam; the
remaining three — the recovery seed's width, the decision row stage's query
count, and the Case-2 copy count — are the same rewrite applied to their own
stages, and the bank already supplies each numeral in the same frame.
-/

namespace NearCubicWires.BankRefuterWordFrameProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RefuterWordFrameProgram
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

/-! ## 2. The register-driven request prelude

Input the bank's frame
`pair sourceLength (pair width (pair queryCount (pair copies pointCode)))`,
output the published refuter's call frame
`pair (pair description sourceLength) (pair sourceLength pointCode)`.  The
scheduled source length is now a register read; the description is the only
immediate. -/

/-! ## 3. The truncation adapter

Input `pair outputCode (pair sourceLength pointCode)`, output
`pair (bitInputPrefixInput sourceLength outputCode) (pair sourceLength
pointCode)`. -/

/-! ## 4. The published refuter call -/

/-! ## 5. The frame -/

/-! ## 6. The Case-1 chain from the bank's frame

Linking the register-driven frame onto the published Case-1 compiler closes the
first of the four baked numerals: `CaseOneTargetLanguageClosure`'s scheduled
source length is now a register read.  The recovery seed's width remains the
one numeral this chain still takes as an immediate, and the decision row stage
`row` is unchanged.
-/

end NearCubicWires.BankRefuterWordFrameProgram
