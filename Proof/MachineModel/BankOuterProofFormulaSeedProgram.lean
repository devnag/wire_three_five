import Proof.MachineModel.BankRefuterWordFrameProgram

/-!
# The Case-1 recovery seed, with the scheduled width read rather than baked

`BankRefuterWordFrameProgram.run_bankCaseOneTargetBitProgram` reads the
scheduled *source length* from the numeral bank's registers, but the Case-1
chain still carries one target-derived immediate: the scheduled width, frozen
by the `set` instruction of
`OuterProofRecoveryFormulaSeedProgram.outerProofSeedPreludeProgram`.

That immediate cannot be replaced by a read of the numeral bank's width
register, because the seed runs inside a native context call and sees only the
refuter word.  It does, however, see the *public length* — and on the Case-1
chain that public length is precisely the scheduled source length the bank
itself decodes the width from.  `RuntimeScheduleNumeralBank.widthEnvelopeProgram`
is the bank's width stage as a standalone stream, so the seed can recompute the
width from its own length register.

This module performs that swap.  §1 lifts the public length beside the retained
refuter word, §2 runs the width stage on it and reassembles the exact frame
`outerProofSeedPreludeOutput` produced, and §3 re-derives the composed seed run
with the published tail of `OuterProofRecoveryFormulaSeedProgram` unchanged.
The resulting program's only parameters are the named decision row stage and
the three *frozen* published shape numerals `(clockDepth, coefficient,
exponent)`; no request-derived numeral appears anywhere in the stream.
-/

namespace NearCubicWires.BankOuterProofFormulaSeedProgram

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. The public length beside the retained request -/

/-! ## 2. The prelude frame with the computed width -/

/-! ## 3. The composed seed, with no width immediate -/

/-! ## 4. The scheduled instance

At a request whose public length is the scheduled source length, the recomputed
width is the chain's own scheduled width: this is
`RuntimeScheduleNumeralBank.bankWidth_at_sourceLength`, and the budget's
positivity is `publishedWidthBudget_positive`.
-/

end NearCubicWires.BankOuterProofFormulaSeedProgram
