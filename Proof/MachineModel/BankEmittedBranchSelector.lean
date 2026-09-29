import Proof.MachineModel.BankDispatchedTargetBody
import Proof.MachineModel.EmittedBranchTargetProgram

/-!
# The dispatcher's selector, supplied by the emitter at the bank's frame

`BankDispatchedTargetBody.inverse_bodyRun_of_dispatch` discharges `bodyRun`
from four premises: the selector's two tags and the two chains' values, each
stated at the numeral bank's own frame.  The two chain premises are the
subject of the fleet's register-driven stages; the two selector premises are
the subject of this module.

`BankRecoveryCodeProgram.run_emittedBranchSelectorProgram_caseOne` and its
Case-2 twin already remove every query immediate from the selector: they take
the request code and the retained point code as *parameters* and consume one
emitter premise.  Instantiating both parameters with the bank's frame therefore
turns the two tag lemmas into exactly the two premises the dispatcher wants,
and leaves one statement about one program:

> started on the bank's frame at public length `target`, the emitter returns
> the tagged inverse-schedule atom stream beside that same frame.

That statement is `InverseEmitterRuns` below.  §3 discharges `bodyRun` from it
together with the two chain premises, so on the inverse schedule the selector
side of the dispatched body is closed by a single emitter-run hypothesis.

## What the emitter hypothesis still needs

`StructuralAtomCalleeProgram.run_emittedBranchSelectorProgram_ofCompiler` runs
the atom emitter from the *loop's* input frame
`pair (generatedBalancedRangeInput count context) pointCode` and from the
nested compiler's own run.  Two things separate that from `InverseEmitterRuns`:
the bank's frame must be lowered to the loop's input frame — one stage that
reads the frame's registers, computes the projection-runner table and the
formula length, and retains the frame — and the atom schedule must be read at
an *executable* presentation of `paddedOuterPCP outer`, which this tree does
not yet construct.  `BankEmittedAtomLoop` records both as one named hypothesis
each and discharges `InverseEmitterRuns` from them.
-/

namespace NearCubicWires.BankEmittedBranchSelector

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The emitter premise at the bank's frame -/

/-! ## 2. The selector's resource envelopes at the bank's frame -/

/-! ## 3. `bodyRun` from the emitter premise and the two chains -/

end NearCubicWires.BankEmittedBranchSelector
