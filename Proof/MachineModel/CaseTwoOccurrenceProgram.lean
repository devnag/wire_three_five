import Proof.CaseAnalysis.CaseTwoOccurrenceRunnerCalls
import Proof.MachineModel.CanonicalLiteralDecodeProgram
import Proof.MachineModel.CaseTwoOccurrenceParityProgram

/-!
# The assembled Case-2 occurrence program

`CaseTwoOccurrenceEvaluation.executableOccurrenceValue_prefixView` reduces one
honest occurrence bit of the published factory to `occurrenceCodeValue`: four
runner executions, one interior digit window, one masked parity fold, and one
digit read.  Every one of those pieces already has an exact interpreter run:

* `CaseTwoOccurrenceRunnerCalls.run_shapeCallProgram`, `…_clauseCallProgram`,
  `…_supportCallProgram`, `…_honestCallProgram`;
* `CanonicalBitSliceProgram.run_bitSliceProgram`;
* `CanonicalLiteralDecodeProgram.run_literalDecodeProgram`;
* `CaseTwoOccurrenceParityProgram.run_maskedParityProgram`.

This module supplies the missing wiring and nothing else.  Every declaration
below is either one straight-line framing adapter — a fixed sequence of
`unpair`, `pair`, `add`, `subtract`, and `testBit` instructions moving already
computed naturals between the published call ABIs — or one application of the
verified linker, the count-preserving wrapper, and the fixed tag dispatcher.
No new mathematics, no callback, and no second occurrence convention is
introduced.

The single assignment dispatch is the saturating difference
`systematicBits - index`: it vanishes exactly on the auxiliary indices.  One
`supportRunner` call therefore suffices per occurrence, because the selected
literal names a single assignment coordinate.
-/

namespace NearCubicWires.CaseTwoOccurrenceProgram

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalLiteralDecodeProgram
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceParityProgram
open NearCubicWires.CaseTwoOccurrenceRunnerCalls
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.TaggedProgramChoice
open NearCubicWires.UnaryPolynomialSelector
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping shared by every framing adapter -/

/-! ## 2. The framing words

Six fixed context words carry the already computed naturals of one occurrence
between the published call ABIs.  Each is a right-nested `Nat.pair` chain, so
every field is bounded by the word itself and no adapter needs a width
argument of its own. -/

/-! ## 3. Straight-line framing adapters -/

/-! ### 3.1 Preparing the shape call

Register ABI: `r2` arity, `r3` request tail, `r4` circuit-and-code pair, `r5`
encoded circuit, `r6` native request, `r7` context. -/

/-! ### 3.2 Reading the shape widths and preparing the clause address -/

/-!
Register ABI: `r2` shape code, `r3` context, `r4` arity, `r5` circuit-and-code
pair, `r6` encoded circuit, `r7` occurrence code, `r8` systematic width, `r9`
shape tail, `r10` auxiliary width, `r11` clause width, `r12` assignment width,
`r13` position index, `r14` position digit, `r15` new context, `r16` slice
request.
-/

/-! ### 3.3 Preparing the clause call -/

/-!
Register ABI: `r2` clause address, `r3` context, `r4`–`r6` context tails, `r7`
arity, `r8` circuit-and-code pair, `r9` encoded circuit, `r10` native request.
-/

/-! ### 3.4 Selecting the occurrence literal and preparing its decode -/

/-!
Register ABI: `r2` clause code, `r3` context, `r4` position digit, `r5`
selected literal code, `r6`–`r7` context tails, `r8` assignment width, `r9`
decode request.  Both selection arms cost the same two instructions, so the
adapter has one fuel charge.
-/

/-! ### 3.5 Dispatch tag and branch payload -/

/-!
Register ABI: `r2` decoded literal, `r3` context, `r4` complement tag, `r5`
assignment index, `r6`–`r9` context tails, `r10` dispatch tag, `r11` branch
context, `r12` branch payload.
-/

/-! ### 3.6 Preparing the systematic support call -/

/-!
Register ABI: `r2` index, `r3` context, `r4` complement tag, `r5`–`r6` context
tails, `r7` arity, `r8` circuit-and-code pair, `r9` encoded circuit, `r10`
occurrence code, `r11` native request, `r12` parity context.
-/

/-! ### 3.7 Preparing the masked parity fold -/

/-!
Register ABI: `r2` support word, `r3` context, `r4` complement tag, `r5`
arity-and-code pair, `r6` arity, `r7` occurrence code, `r8` range request.
-/

/-! ### 3.8 Preparing the auxiliary honest call

The honest runner consumes the canonical code of its own input arity, which
is exactly the zero-offset digit window of the public occurrence code.  The
adapter therefore emits one `bitSliceProgram` request and keeps the auxiliary
index beside it. -/

/-!
Register ABI: `r2` index, `r3` context, `r4` complement tag, `r5` context
tail, `r6` systematic width, `r7` arity-and-circuit frame, `r8` arity, `r9`
circuit-and-code pair, `r10` encoded circuit, `r11` occurrence code, `r12`
honest context, `r13` window offset, `r14` slice request.
-/

/-! ### 3.9 Framing the honest call itself -/

/-!
Register ABI: `r2` prefix code, `r3` context, `r4` complement tag, `r5`
context tail, `r6` systematic width, `r7` index frame, `r8` index, `r9`
arity-and-circuit pair, `r10` arity, `r11` encoded circuit, `r12` native
request, `r13` digit context.
-/

/-! ### 3.10 Reading the auxiliary digit -/

/-!
Register ABI: `r2` honest word, `r3` context, `r4` complement tag, `r5`
width-and-index pair, `r6` systematic width, `r7` index, `r8` auxiliary
offset, `r9` assignment digit.
-/

/-! ### 3.11 The complementing exclusive-or suffix -/

/-!
Register ABI: `r2` assignment digit, `r3` complement digit, `r4` sum, `r5`
constant zero.  Adding two digits and reading digit zero of the sum is
exclusive-or.
-/

/-! ## 4. Linking at one charged width

Every composition below is one application of `run_occurrenceStage`, so no
width comparison in this module is deeper than two `max` levels. -/

/-! ## 5. The systematic assignment branch

One support-runner call at the selected index, followed by the fixed masked
parity controller of `CaseTwoOccurrenceParityProgram`. -/

/-! ## 6. The auxiliary assignment branch

One honest-runner call on the low digit window of the occurrence code,
followed by a single digit read at the auxiliary offset. -/

/-! ## 7. Derived coordinates of one occurrence request -/

/-! ## 8. The assembled occurrence program -/

end NearCubicWires.CaseTwoOccurrenceProgram
