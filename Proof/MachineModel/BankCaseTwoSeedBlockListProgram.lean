import Proof.MachineModel.BankScheduleDiagonal

/-!
# The Case-2 seed block list, driven from the numeral bank's registers

`CaseTwoSeedBlockListProgram.caseTwoSeedBlockListProgram` carries exactly one
target-derived immediate: the XOR copy count, frozen by the `set` instruction
of `caseTwoBlockRangePrepProgram`.  On the fixed schedule that immediate is
harmless — `RecoveryScheduleEnvelope.fixedCopies` does not depend on the
scheduled width, so `EmittedBranchTargetProgram.fixedCaseTwoChainProgram_target_independent`
already records that the whole chain is request-independent.  On the *inverse*
schedule the copy count is `inverseCopies outer pcppSource rate sourceIndex`,
which grows with the scheduled width, and the immediate is therefore the last
target-derived numeral of the Case-2 branch.

`RuntimeScheduleNumeralBank` leaves that very numeral in a register: the bank's
frame is

`pair sourceLength (pair width (pair queryCount (pair copies pointCode)))`.

This module replaces the prep stage's `set` by three `unpairRight`
instructions, so the range generator's input `pair copies pointCode` is read
rather than baked, and re-derives the composed run of the block-list stage, of
the Case-2 target bit, and of the inverse schedule's Case-2 chain — all from
the bank's frame, with no schedule immediate anywhere in the stream.

The single remaining parameter is unchanged: the per-block occurrence callee of
`CaseTwoSeedBlockListProgram`.
-/

namespace NearCubicWires.BankCaseTwoSeedBlockListProgram

open NearCubicWires
open NearCubicWires.BankScheduleDiagonal
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.CaseTwoTargetLanguageClosure
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The range request, read from the bank's copy register -/

/-! ## 2. The block-list stage from the bank's frame -/

/-! ## 3. The Case-2 target bit from the bank's frame -/

/-! ## 4. The inverse schedule's Case-2 chain, from the bank's frame

On the diagonal — a request whose public length is the scheduled source length
the inverse chain works at — `BankScheduleDiagonal.publishedBankFrame_at_inverseDiagonal`
identifies the bank's frame with the chain's own numerals.  The copy register
is then literally the inverse schedule's XOR copy count, so §3 applies with no
schedule immediate anywhere in the stream.
-/

end NearCubicWires.BankCaseTwoSeedBlockListProgram
