import Proof.CaseAnalysis.CaseTwoTargetLanguageClosure
import Proof.MachineModel.RuntimeLeftShiftProgram

/-!
# The Case-2 seed block list, from the requested point code

`CaseTwoTargetLanguageClosure` leaves exactly one stage of the Case-2 branch as
a hypothesis: the loop that evaluates the scheduled Case-2 seed once per XOR
copy and hands the resulting block list to the fixed target-bit dispatcher.
This module builds that loop.

The construction is the same one `OuterProofRecoveryFormulaSeedProgram` uses
for the C.12 clause stream: `GeneratedBalancedRangeProgram` materializes the
`copies` request atoms directly in the canonical balanced representation, and
`CanonicalBalancedCall` runs one callee per atom.  Two straight-line framing
adapters bracket the pair — one building the range request from the requested
point code, one attaching the Case-2 dispatch tag — and one more drops the
context the range generator retains.

Two mathematical bridges make the result usable.

* `bitSlice_encodeBitInput_blockInput` identifies the interior digit window of
  the requested point code at offset `block * arity` with the code of that
  block's own restriction, so the per-block callee never needs the whole point.
* `xorPower_eq_foldl_range` replaces the choice-selected enumeration
  `Finset.univ.toList` inside `xorPower` by the machine's own `List.range`
  order.  Both lists enumerate `Fin copies` without repetition, and the parity
  fold is invariant under permutation.

The single remaining parameter is the per-block occurrence callee: one program
receiving `pair block pointCode` at the public target length and returning the
honest occurrence bit of the published factory at that block's occurrence code.
`CaseTwoOccurrenceProgram.run_caseTwoOccurrenceProgram` already executes the
occurrence itself; what the callee still has to add in front of it is the
occurrence-code assembly, whose only non-straight-line ingredient — scaling by
a run-time power of two — is `RuntimeLeftShiftProgram`.
-/

namespace NearCubicWires.CaseTwoSeedBlockListProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceCoordinates
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoTargetLanguageClosure
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. The parity fold does not see the enumeration order -/

/-! ## 2. One block of the requested point is one digit window -/

/-! ## 3. The per-block occurrence value -/

/-! ## 4. The three framing adapters -/

/-! ## 5. The block-list stage -/


/-! ## 6. The Case-2 target bit from the requested point code -/

/-! ## 7. Both published schedules -/

end NearCubicWires.CaseTwoSeedBlockListProgram
