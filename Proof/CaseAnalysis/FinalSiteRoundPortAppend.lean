import Proof.CaseAnalysis.RowsEstimatorAppendPadded
import Proof.CaseAnalysis.RowsEstimatorParityCounter
import Proof.CaseAnalysis.FinalExactRecordLoop
import Proof.CaseAnalysis.FinalRoundBudget

/-! The physical record/count append segment of a C.10 site round.

The local record is an explicit produced-input precondition. The same fixed
four-tape machine appends its six fields to an arbitrary existing stream and
increments the existing unary record count. It returns the record cursor and
the same padded reset log, so a second operation reuses both tapes literally.
The copy's 40*b+56 includes its cursor restore; the counter pays 2*n+2; their
composition pays one bridge step. No empty-scratch restoration is assumed.

This segment starts/ends with the stream at its append cursor and the count
at head 1. The enclosing hsite starts/ends with ALL heads at 0. Its seek/rewind
and actual record producer are still separate typed obligations; this file
does not assert hsite or supply those operands for free.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPortAppend

open LocalBitMultitape ExtDecompositionBatch RecoveryRootRound
open RepairSource.VerifierDecoding
open CloseoutRowsEstimatorCoefficients

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

def countSlot (_ : Fin 1) : Fin 4 := 3

noncomputable def machine := Composition.machine
  (TapeEmbedding.machine 1 CloseoutRowsEstimator.AppendCopy.machine)
  (RecoveryFocus.machine countSlot CloseoutRowsEstimatorParity.Counter.machine)

def budget (width count : ℕ) : ℕ := (40 * width + 56) + 1 + (2 * count + 2)

def twiceBudget (width count : ℕ) : ℕ := budget width count + 1 + budget width (count + 1)


end NearCubicWires.RepairOrdinary.CloseoutFinalC10SiteRoundPortAppend
