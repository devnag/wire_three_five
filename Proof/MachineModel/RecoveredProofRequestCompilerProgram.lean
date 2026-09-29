import Proof.MachineModel.GeneratedBalancedRangeProgram
import Proof.MachineModel.RecoveredProofEncodingProgram

/-!
# The recovered-proof request compiler

`RecoveredProofEncodingProgram.run_recoveredProofEncodingProgram` consumes one
public code, `recoveredProofEncodingInput`, that is `encodeBalancedList` of the
whole address schedule of the C.12-recovered outer proof.  That list is
exponentially long, so it may not be supplied as data: a fixed program has to
build it.  This module is that builder.

Only two ingredients are used, both already certified elsewhere.

* `GeneratedBalancedRangeProgram` emits the canonical balanced list of the
  consecutive request atoms `pair inputLength (pair address stream)` directly,
  without materializing a linked spine.
* One canonical balanced call reshapes every atom into the exact prefix-SAT
  request `pair inputLength (pair stream (encodeUnary (address + 1)))` demanded
  by `RecoveredProofEncodingProgram.recoveredProofRequest`.  The tiny fixed
  callee is the only new instruction stream here; it performs no oracle query.

The composed program is therefore oracle-free: every SAT query of Case 1 still
happens inside the already published `recoveredProofEncodingProgram`.

## What remains outside

The compiler needs the raw clause stream of `outerProofRecoveryFormula` and the
proof address count `2 ^ scheduledWidth` in its input register.  Producing that
seed pair from the raw refuter word is one further fixed program — the *only*
remaining seam of the Case-1 request path — so it enters the theorems below as
an explicit program together with its own exact run hypothesis, exactly as
`CanonicalNativeCallProgram.run_nativeCallProgram` takes its callee.
-/

namespace NearCubicWires.RecoveredProofRequestCompilerProgram

open NearCubicWires
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalBinaryProgram
open NearCubicWires.CanonicalRecoveryLanguage
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.RecoveredProofEncodingProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralClauseStreamProgram
open NearCubicWires.VerifiedLinker

/-! ## 1. Monotonicity of the unary loop bound -/

/-! ## 2. One request atom

The callee receives the range generator's atom body `pair address stream` in
register zero and the shared public length in register one.  It returns the
canonical prefix-SAT request of that address. -/

/-! ## 3. The atom-indexed call schedule -/

/-! ## 4. Dropping the generator's retained context -/

/-! ## 5. The whole request list from one count and one clause stream -/

/-! ## 6. The scheduled instance

At the published schedule the generated list is literally
`recoveredProofEncodingInput`, so `run_recoveredProofEncodingProgram` may be
invoked immediately afterwards. -/

/-! ## 7. The request compiler

The compiler is the seed stage followed by the request-list builder run on the
seed's left component; the retained right component is the
`(calleeInputLength, context)` frame consumed by
`CanonicalNativeCallProgram.nativeContextCallProgram`, so the published
encoder can be called immediately afterwards without recomputing the schedule
parameters. -/

end NearCubicWires.RecoveredProofRequestCompilerProgram
