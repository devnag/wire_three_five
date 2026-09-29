import Proof.MachineModel.BranchTargetLanguageProgram

/-!
# The per-block Case-2 occurrence callee

`CaseTwoSeedBlockListProgram` closes the Case-2 branch of the canonical target
modulo exactly one parameter: a program receiving `pair block pointCode` at the
public target length and returning the honest occurrence bit of the published
factory at that block's occurrence code.  This module builds that program.

Nothing new is computed.  The occurrence itself is already executed by
`CaseTwoOccurrenceProgram.run_caseTwoOccurrenceProgram`; what has to be added
in front of it is the occurrence-code assembly of
`CaseTwoOccurrenceCoordinates.nativeOccurrenceCode`, which is

* one product `block * arity`, the block's digit offset in the requested point
  code — `CanonicalBitSerialMulProgram`;
* three interior digit windows — `CanonicalBitSliceProgram`: the block window
  itself, then its low input window and its interior clause window;
* one occurrence position digit — the register-indexed `testBit` opcode;
* two scalings by a run-time power of two — `RuntimeLeftShiftProgram`;
* two additions.

Seven straight-line framing adapters move those already computed naturals
between the published call ABIs, and the whole chain is assembled with the
verified linker and the count-preserving wrapper.  No oracle query, no
callback, and no second occurrence convention is introduced: the only oracle
opcode anywhere below the target dispatcher is the branch selector's, which
lives elsewhere.

The circuit data — arity, size, and encoding — are immediates of the stream,
exactly as the XOR copy count is an immediate of the block-list stage.  They
are supplied by the caller rather than recomputed inside the callee.
-/

namespace NearCubicWires.CaseTwoBlockOccurrenceProgram

open NearCubicWires
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalBitSerialMulProgram
open NearCubicWires.CanonicalBitSliceProgram
open NearCubicWires.CanonicalTargetBitProgram
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceCoordinates
open NearCubicWires.CaseTwoOccurrenceEvaluation
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoOccurrenceSpecification
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoSeedBlockListProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PCPPClausePadding
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeLeftShiftProgram
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping shared by every framing adapter -/

/-! ## 2. The block window of the requested point code

Register ABI of both adapters: `r2` the leading field of the request, `r3` its
trailing field, `r4` the block arity immediate, `r5` the assembled callee
request. -/

/-! ### The window chain -/

/-! ## 3. The native occurrence code of one block window

Three windows of the block window are repacked into the occurrence ABI of
`CaseTwoOccurrenceProgram`.  The occurrence position digit is read first, by a
single register-indexed `testBit`, so that the block window itself may be
consumed by the two remaining slices. -/

/-! ### 3.1 The low input window and the position digit

Register ABI: `r2` the position index, `r3` the position digit, `r4` the
retained context, `r5`/`r6` the slice immediates, `r7`/`r8` the slice
request. -/

/-! ### 3.2 The interior clause window

Register ABI: `r2` the low window, `r3` the retained context, `r4` the position
digit, `r5` the block window, `r6` the new context, `r7`/`r9` the slice
immediates, `r8`/`r10` the slice request. -/

/-! ### 3.3 The two scalings and the digit sum

The instruction set's `shiftLeft` takes a compile-time amount only, so both
scalings go through `RuntimeLeftShiftProgram`.  Register ABI of the two
adapters: `r2` the value to scale, `r3` the retained context, `r4`/`r5` its
fields, `r6` the running sum, `r7` the exponent, `r8` the shift request. -/

/-! ### 3.4 The native occurrence code chain -/

/-! ## 4. The assembled per-block occurrence callee

Register ABI of the last adapter: `r2` the encoded circuit, `r3` the encoded
request tail, `r4` the circuit size, `r5` the sized tail, `r6` the circuit
arity. -/

/-! ## 5. The callee at the scheduled Case-2 coordinates

Instantiating §4 at the substituted circuit of the recovered oracle gives
exactly the value `CaseTwoSeedBlockListProgram` asks its per-block parameter
for.  The circuit's arity, size, and encoding, the two padded widths, the
native clause width, and the block arity are the stream's immediates. -/

/-! ## 6. The Case-2 chains with the occurrence parameter discharged

Both published schedules now carry no per-block hypothesis at all: the whole
Case-2 branch is one fixed instruction stream over the scheduled immediates. -/

end NearCubicWires.CaseTwoBlockOccurrenceProgram
