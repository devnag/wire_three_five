import Proof.MachineModel.CanonicalBranchSelectorProgram

/-!
# The length-driven schedule decoder

`CanonicalTargetLanguageProgram.executableLanguageProgramOfRun` demands *one*
instruction stream for every `LanguageEvaluationRequest`, whereas the two
chains of `BranchTargetLanguageProgram` still carry the scheduled numerals as
immediates chosen from the request's own target length.  Every such numeral is
a function of `LanguageEvaluationRequest.length` through the sole source
enumeration: `RecoveryScheduleEnvelope.sourceIndexOfLength` decodes the index,
`RecoveryScheduleEnvelope.sourceLength` is `2 ^ (index + 1)`, and the widths,
caps, and copy counts are arithmetic in that length and the published
constants.

This module supplies the first, length-only stage of that decoder: from the
request alone it emits the scheduled source index and the scheduled source
length beside the retained request code, in the framed shape

`pair sourceIndex (pair sourceLength code)`.

Two already verified programs do the work — `sourceIndexProgram`, whose only
input is the public length register, and `binaryTwoPowProgram` — bracketed by
three straight-line framing adapters and the count-preserving wrapper.  The
decoder is oracle-free, and its width and fuel are closed in the public
length alone.

## What the decoder cannot supply

Two of the numerals the chains bake are *not* arithmetic in the public length:

* `outer.pcp.queryCount` at the scheduled length is an opaque field of the
  projection PCP, bounded only from above by the published contract, exactly
  the datum whose positivity `BranchTargetLanguageProgram` already carries as
  an explicit Case-1 hypothesis;
* the Case-2 substituted circuit's encoding depends on the recovered oracle,
  not on the request, and is produced by the bounded-oracle description
  recovery rather than by schedule arithmetic.

Both are recorded at the packaging seam rather than hidden here.
-/

namespace NearCubicWires.LanguageScheduleDecoderProgram

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

/-! ## 2. The three framing adapters -/

/-! ## 3. The decoder -/

/-! ## 4. The decoder at one language request -/

end NearCubicWires.LanguageScheduleDecoderProgram
