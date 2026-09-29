import Proof.MachineModel.CanonicalBalancedNatSumProgram
import Proof.MachineModel.CanonicalProjectedRandomBitProgram
import Proof.MachineModel.CanonicalThreeCNFLiteralProgram
import Proof.MachineModel.OuterProofRecoveryFormulaSeedProgram

/-!
# The decision-row emitter of the C.12 recovery formula

`OuterProofRecoveryFormulaSeedProgram` reduces the whole Case-1 recovery seed
to one named row stage: from `pair code (pair width (encodeBitInput input))` it
must emit

```text
rawClauseStream (outerProofRowFormula pcp input (bitInputOfCode width code))
```

which is definitionally `encodeTaggedList (outerProofRowStream pcp input code)`.

This module owns that stage.

Section 1 is the semantic seam: one raw arithmetic normal form of the row
stream whose only imported data are

* the published query runner's projection code at every `(query, bit)`
  coordinate of the *native* width, folded into `binaryAddress`;
* the published decision runner's single output at the native prefix of the
  requested randomness, read through the canonical `ThreeCNF` codec.

Nothing else about the padded PCP enters: the padded width contributes only
the constant-zero high address bits, which the fold below never visits.

Sections 2 and 3 build the executable address side of that normal form.  One
published balanced range, one published balanced call and the published
balanced natural-number sum fold the coordinates of a single query index into
its proof-table address; a second published range and call apply that stage at
every query index, so one fixed oracle-free program emits the whole address
table of a row as a balanced list.  Both stages are stated modulo the single
named coordinate callee, whose contract is the hypothesis `hweight` of
`run_rowAddressProgram`: from `pair bit (rowWeightContext …)` it must emit
`rowAddressWeight native randomnessCode bit (projection bit)` — one
`pcp.query` call framed by `preserveRightProgram`, the published
`projectedRandomBitProgram`, and the published dyadic exponential.
-/
namespace NearCubicWires.OuterProofRowProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedNatSumProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionPCPPadding
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.TseitinCNF
open NearCubicWires.VerifiedLinker

/-! ## 1. The raw-code specification of one decision row -/

/-! ### The address fold is the padded query address -/

/-! ### The decision code is the padded decision row -/

/-! ### The raw stream is the padded decision row -/

/-! ### The scheduled instance of the seam -/

/-! ## 2. The address stage of one query index

One published balanced range, one published balanced call, and the published
balanced natural-number sum turn the coordinate callee of a single query index
into its complete proof-table address. -/

/-! ## 3. The address table of one decision row

A second published range and call apply the address stage at every query index,
so one fixed program emits the whole address table of a row as a balanced list.
-/

end NearCubicWires.OuterProofRowProgram
