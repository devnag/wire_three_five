import Proof.MachineModel.CaseTwoOccurrenceProgram

/-!
# The scheduled Case-2 occurrence coordinates as one natural code

`CaseTwoOccurrenceSpecification.caseTwoSeed_apply_executable` evaluates the
published factory at `caseTwoOccurrenceCoordinates`, which drops the two
scheduled padding axes from the requested seed point.  Both drops —
`projectPaddedSystematicOccurrenceInput` on the input axis and
`projectPaddedOccurrenceInput` on the clause axis — are plain index gathers:
each coordinate of the result is one coordinate of the request.

This module reads that gather off a single natural code.  The three windows
involved are exactly the ones the executable stack already has:

* the low input window, `bitSlice 0 _`, also computed by
  `BitInputPrefixProgram.bitInputPrefixProgram`;
* the interior clause window, `bitSlice`, computed by
  `CanonicalBitSliceProgram.bitSliceProgram`;
* the single occurrence position digit, one `testBit`.

`nativeOccurrenceCode` repacks those three windows into the occurrence ABI of
`CaseTwoOccurrenceProgram`, and `caseTwoOccurrenceCoordinates_prefixView` is
the exact identification.  Combined with
`CaseTwoOccurrenceEvaluation.executableOccurrenceValue_prefixView` and the
contract `caseTwoSeed_apply_executable`, this yields the executable seed bit at
every scheduled Case-2 coordinate.
-/

namespace NearCubicWires.CaseTwoOccurrenceCoordinates

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces

/-! ## 1. Digit composition of two adjacent blocks -/

/-! ## 2. The native occurrence code -/

/-! ## 3. Both padding drops are one digit window -/

/-! ## 4. The scheduled Case-2 instance -/

end NearCubicWires.CaseTwoOccurrenceCoordinates
