import Proof.MachineModel.CanonicalBalancedLookupProgram
import Proof.MachineModel.CanonicalBitSerialMulProgram
import Proof.CaseAnalysis.CaseOneTargetLanguageClosure
import Proof.MachineModel.OuterProofRowProgram

/-!
# The decision-row stage of the C.12 recovery formula, executed

`OuterProofRowProgram` reduced one decision row to three named frontiers: the
coordinate callee of its address fold, the per-clause emitter of its raw clause
list, and the top assembly that joins them.  This module discharges all three
and instantiates the resulting Case-1 chain.

Section 1 builds the coordinate callee whose contract is the `hweight`
hypothesis of `run_rowAddressProgram`: from `pair bit (rowWeightContext …)` a
straight-line prelude frames the published query runner's own request code, the
published query runner returns the projection code, a second frame builds the
published projected-random-bit request, and the published dyadic exponential
followed by the published bit-serial multiplier turn the resulting bit into its
weighted contribution.

Section 2 builds the per-clause emitter: three applications of the published
`ThreeCNF` literal codec, each re-signed and redirected through one published
balanced lookup into the row's own address table, assembled into the singleton
tagged clause list consumed by the published clause-stream flattener.

Section 3 assembles the whole row: the published low-bit normalizer selects the
native randomness, the published decision runner emits the decision code, the
address table of `OuterProofRowProgram` supplies every proof-table address, and
one published range, call and flattener emit the row's raw clause stream.

Section 4 instantiates the Case-1 chain: `hrow` is discharged, so both the
recovery seed and the Case-1 target bit run unconditionally.
-/
namespace NearCubicWires.OuterProofRowStageProgram

open NearCubicWires
open NearCubicWires.BalancedClauseStreamFlattenProgram
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBalancedLookupProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalEncodedListLengthProgram
open NearCubicWires.CanonicalEncodedListLookupProgram
open NearCubicWires.CanonicalProjectedRandomBitProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalThreeCNFLiteralProgram
open NearCubicWires.CanonicalTwoPowProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseOneTargetLanguageClosure
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.OuterProofRecoveryFormulaSeedProgram
open NearCubicWires.OuterProofRowProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveredProofCaseOneProgram
open NearCubicWires.RecoveredProofRequestCompilerProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 0. Shared helpers -/

/-! ## 1. The coordinate callee of the address fold -/

/-! ### The query-uniform envelope consumed by the address table -/

/-! ## 2. The per-clause emitter -/

/-! ### The literal stage, addressed by its position numeral -/

/-! ### The three literals of one clause -/

/-! ### The composed clause emitter -/

/-! ## 3. The raw clause stream of one decision row -/

/-! ### The address-table half of the row -/

/-! ### The two scheduled numerals, read at run time

Both numerals the row needs — the native randomness width and the query count —
are the two components of `ExecutableProjectionPCP.shapeCode`, and that code is
produced by the published shape runner from the public length alone.  Register
one carries that public length through every linked stage, so each stage that
needs a numeral reloads it, runs the shape program and unpairs.  No numeral is
ever an immediate, and no frame above the row changes shape. -/

/-! ### The composed address-table half -/

/-! ### The whole decision row -/

/-! ## 4. The Case-1 chain, unconditionally -/

/-! ### The Case-1 recovery seed -/

/-! ### The Case-1 target bit from the requested point code -/

/-! ### Both published schedules -/

end NearCubicWires.OuterProofRowStageProgram
