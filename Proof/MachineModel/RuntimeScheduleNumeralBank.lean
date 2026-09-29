import Proof.MachineModel.CanonicalNatCeilLogProgram
import Proof.MachineModel.LanguageScheduleDecoderProgram

/-!
# The run-time schedule numeral bank

`LanguageScheduleDecoderProgram` turns the two purely enumerative numerals —
the scheduled source index and the scheduled source length — into run-time
registers.  Every other numeral the two chains of `BranchTargetLanguageProgram`
still bake as an immediate is arithmetic in that length together with numerals
that do *not* vary with the request: the published outer shape coefficient and
proof exponent, the pairing-clock depth, the recovery block, and the scheduled
rate.  This module supplies the arithmetic.

Three groups of fixed programs are built.

* §2 collects the value-level primitives that the schedule arithmetic needs and
  that no earlier module exposes: iterated self-pairing (the pairing clock),
  the base-two *floor* logarithm (obtained from the published ceiling
  logarithm, not from a second loop), `Semantics.logScale`, immediate
  multiplication and addition, and the fixed-exponent power.
* §3 collects the straight-line framing adapters that move one numeral between
  the head of the frame and its retained context.
* §4 assembles the two composite numerals — the scheduled width
  `RecoveryScheduleEnvelope.scheduledWidth`, i.e. the base-two logarithm of the
  published width budget, and the scheduled copy count of
  `RecoveryScheduleEnvelope.inverseCopiesOf`/`fixedCopiesOf` — and §5 the bank
  itself.

## What the bank does and does not decide

The bank is oracle-free except for the single imported shape runner call, and
it is closed in `(publicLength, frozen numerals)`.  The scheduled query count is
*not* schedule arithmetic — it is an opaque field of the projection PCP — but it
is nevertheless run-time data: `ExecutableProjectionPCP.queryCount` is by
definition the right component of `pcp.shape.execute`, and `pcp.shape` is an
executable program.  §5 therefore reads it with one
`CanonicalNativeCallProgram.nativeContextCallProgram` call on that runner rather
than as an immediate, which removes it from the list of data that force the
instruction stream to depend on the request.

The one datum the bank does not produce is the Case-2 substituted circuit's
encoding, which is recovered from the accepting oracle rather than computed from
the request.
-/

namespace NearCubicWires.RuntimeScheduleNumeralBank

open NearCubicWires
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalNatCeilLogProgram
open NearCubicWires.CanonicalNativeCallProgram
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.LanguageScheduleDecoderProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping -/

/-! ## 2. Value-level primitives -/

/-! ### Iterated self-pairing -/

/-! ### The base-two floor logarithm -/

/-! ### The manuscript's logarithmic scale -/

/-! ### Immediate multiplication and addition -/

/-! ### The fixed-exponent power -/

/-! ## 3. The two composite schedule numerals

The three numerals below are the exact values of
`ProjectionWidthEnvelope.widthBudget`, `RecoveryScheduleEnvelope.widthEnvelope`
and the copy counts of `RecoveryScheduleEnvelope.inverseCopiesOf`/`fixedCopiesOf`
once the published fields are read as numerals; §6 discharges the identifications.
-/

/-! ## 4. The framing adapters -/


/-! ## 5. The arithmetic front end

The five stages below are linked one at a time: every intermediate frame is a
named program with its own width, clock, and exact-execution theorem, so no
composed instruction span is ever unfolded to justify the next link.
-/

/-! ### The decoded scheduled length -/

/-! ### The scheduled width -/

/-! ### The scheduled copy count -/

/-! ## 6. The scheduled query count and the bank -/

/-! ## 7. The published numerals

Every numeral the bank computes is *definitionally* the published one at the
decoded index; the four identifications below are the whole bridge, and each is
`rfl`.  The published shape runner supplies the one imported execution, and the
published proof-size bound supplies the one side condition.
-/

/-! ## 8. The bank on the scheduled diagonal

At a public length that is itself a scheduled source length the bank's decoded
index is that source's own, so every emitted numeral is the chain's numeral at
that source index.  These are the identities a register-driven chain body uses
to recognize the bank's frame.
-/

end NearCubicWires.RuntimeScheduleNumeralBank
