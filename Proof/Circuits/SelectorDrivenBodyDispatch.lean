import Proof.Circuits.SelectorDrivenEmitterRuns

/-!
# The dispatched bodyRun at an abstract bank frame

Site B-2b of the body-chain replay, stated generically over an abstract frame
function `pointCode`.  The base branch-target run lemmas take the bank frame as
an opaque point code, so these are the frozen proofs of
`BankDispatchedTargetBody.inverse_bodyRun_of_dispatch` /
`BankEmittedBranchSelector.inverse_bodyRun_of_emitterRuns` with the frame kept
abstract — which both avoids the expensive `whnf` on a concrete selector frame
and yields a single lemma reusable at the selector frame.  The selector
schedule's chains are carried as premises.  No `hdiagonal`.
-/

namespace NearCubicWires.SelectorDrivenBodyDispatch

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CanonicalTargetLanguageProgram
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableTargetLanguagePackaging
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SelectorDrivenAtomContextRuns
open NearCubicWires.SelectorDrivenEmitterRuns
open NearCubicWires.SourceInterfaces
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The dispatch width at an opaque frame

The frozen bank body's width mentions `publishedBankFrame`.  That envelope
cannot type a run begun at a different frame: `branchTargetBitBits` charges the
bit length of the retained point code.  Keep the same two-branch maximum, but
parameterize that point code explicitly for the selector-driven replay. -/

/-! ## 4. Chaining to `hexecutes`

`UniformTargetLanguageBank.inverse_hexecutes_of_bodyRun` applied to
`bankDispatchedBodyProgram selector caseOne caseTwo`, its width
`bankDispatchedBodyBits`, its fuel `bankDispatchedBodyFuel`, and the `bodyRun`
of §3 discharges the executable target language's terminal obligation for the
linked stream `bank ⊕ dispatcher`; the packaging's own resource premises
(`hbits`, `hfuel`, `hinitial`, `hrun`, `hboolean`) pass through untouched.
-/



end NearCubicWires.SelectorDrivenBodyDispatch
