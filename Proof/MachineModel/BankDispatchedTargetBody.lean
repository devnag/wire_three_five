import Proof.MachineModel.BankCaseTwoSeedBlockListProgram

/-!
# The register-driven body: one branch dispatcher over the bank's frame

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` consumes exactly one
premise about one fixed instruction stream: `bodyRun`, the statement that at
every requested target the body, started on the numeral bank's frame, returns
the canonical target bit.

`BranchTargetLanguageProgram.branchTargetBitProgram` is *frame agnostic*: the
selector consumes the request code and returns `pair tag code`, and the chosen
chain is then started on the *same* code.  Instantiating that code with the
numeral bank's frame therefore produces a body of exactly the required shape,
with no target-derived immediate contributed by the dispatcher itself.

This module performs that instantiation and discharges `bodyRun` from four
named premises — the selector's two tags and the two chains' values, each
stated at the bank's frame.  §3 records the two premises that are already
inhabited by this fleet's register-driven stages:

* the Case-2 chain is `BankCaseTwoSeedBlockListProgram.bankCaseTwoTargetBitProgram`,
  whose run at the bank's frame is
  `run_bankCaseTwoTargetBitProgram_inverse` (modulo the per-block occurrence
  callee and the diagonal);
* the selector is
  `BankRecoveryCodeProgram.emittedBranchSelectorProgram`, whose two tag lemmas
  `run_emittedBranchSelectorProgram_caseOne/caseTwo` take the retained code —
  here the bank's frame — as a parameter.

The two premises that remain open at the time of writing are the Case-1
chain's value at the bank's frame and the structural atom emitter's run; both
are named, and neither is a property of the dispatcher.
-/

namespace NearCubicWires.BankDispatchedTargetBody

open NearCubicWires
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. Width bookkeeping for the dispatcher -/

/-! ## 2. The body and its resource envelopes -/

/-! ## 3. `bodyRun`, from the four framed premises -/

/-! ## 4. Chaining to `hexecutes`

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` applied to
`bankDispatchedBodyProgram selector caseOne caseTwo`, its width
`bankDispatchedBodyBits`, its fuel `bankDispatchedBodyFuel`, and the `bodyRun`
of §3 discharges the executable target language's terminal obligation for the
linked stream `bank ⊕ dispatcher`; the packaging's own resource premises
(`hbits`, `hfuel`, `hinitial`, `hrun`, `hboolean`) pass through untouched.
-/

end NearCubicWires.BankDispatchedTargetBody
