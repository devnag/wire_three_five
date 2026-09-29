import Proof.PCP.PaddedProjectionPresentation

/-!
# The fixed schedule's `bodyRun`, down to the compiler's run

`HeadlineRootSkeleton` §5 stops at a raw `bodyRun` binder because the whole
chain below `UniformTargetLanguageBank.fixed_hexecutes_of_bodyRun` — the
dispatcher, the emitted branch selector, the atom loop and the executable
presentation — was written only at the inverse schedule.  This module is the
fixed-rate twin of that chain.

## The assessment this module implements

Per inverse module of the `bodyRun` chain:

* **GENERIC, serves both schedules as-is.**  Every *program* on the chain, and
  every run lemma stated at an abstract source index.  In particular
  `BankDispatchedTargetBody.bankDispatchedBodyProgram`/`…Fuel`,
  `BankRecoveryCodeProgram.emittedBranchSelectorProgram` with its two closed
  tag lemmas `run_emittedBranchSelectorProgram_caseOne`/`…_caseTwo`,
  `BankEmittedAtomLoop.inverseBankEmitterProgram` (a schedule-free `linkPrograms`
  of an adapter with the atom-emitter loop),
  `StructuralAtomCalleeProgram.run_structuralAtomEmitterProgram_ofCompiler`,
  `PaddedProjectionPresentation.PresentsPaddedOuterPCP` and its four field
  projections, and `PaddedRunnerBudgetClosure.exists_presentsPaddedOuterPCP_published`,
  which mentions no schedule at all and therefore discharges the presentation
  premise of *both* roots.
* **RENAME-REPLAY.**  Everything schedule-indexed on the chain: the resource
  envelopes (`…Bits`/`…Fuel`), the named premise predicates, and the five
  `bodyRun` reductions.  The substitution is
  `advantageExponent : ℝ ↦ requestedRate : ℕ`,
  `inverseSourceIndex (inverseSelectedSource … (inverseCoreAdvantagePower e) t) ↦
   fixedSelectedSource … r t`,
  `inverseRequiredDegree … (inverseCoreAdvantagePower e) ↦ fixedRequiredDegree … r`,
  `inverseRefuterInput ↦ fixedRefuterInput`,
  `inverseCaseOneTargetOnset ↦ fixedCaseOneTargetOnset`,
  `inverseBankRate ↦ fixedBankRate`, `inverseTargetBranch ↦ fixedTargetBranch`,
  `InverseCaseTwoAcceptance ↦ FixedCaseTwoAcceptance`,
  `inverseCanonicalTargetFunction ↦ fixedCanonicalTargetFunction`.
  No proof term changes.
* **GENUINELY DIFFERENT.**  Only one thing, and it makes the fixed side
  *smaller*: the inverse schedule's chain index carries an extra
  `RecoveryScheduleEnvelope.inverseSourceIndex` search in front of the selected
  source, while the fixed chain's index is the selected source itself.  Every
  fixed statement below is therefore one function application shorter than its
  inverse twin.  `CaseOneRecoveryAssembly.fixedCaseOneTargetOnset` is likewise
  one `max` shorter than the inverse onset, because the fixed advantage reserve
  is target independent.

## The diagonal is still needed, and it is already bridged

The fixed schedule is *not* length-uniform: `RuntimeScheduleNumeralBank` decodes
its source index from the request's own public length, whereas the chain works
at `fixedSelectedSource`, and `bodyRun`'s consumer pins neither.  So the fixed
cluster needs a diagonal hypothesis exactly as the inverse cluster does — but
`BankScheduleDiagonal.publishedBankFrame_at_fixedDiagonal` is already green, so
nothing has to be built for it.  What *is* legitimately frozen on this schedule
is the copy register (`RecoveryScheduleEnvelope.fixedCopies`), which is why
`UniformTargetLanguageBank.fixedBankRate` is the bare `fixedRate`.
-/

namespace NearCubicWires.FixedScheduleAtomLoop

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.BranchTargetLanguageProgram
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The fixed schedule's PCP request -/

/-! ## 2. The loop's generated range at the schedule -/

/-! ## 3. The three named hypotheses -/

/-! ## 4. The dispatcher's width at the fixed bank -/

/-! ## 5. `bodyRun`, from the four framed premises -/

/-! ## 6. The emitter premise at the bank's frame -/

/-! ## 7. The selector's resource envelopes at the bank's frame -/

/-! ## 8. The emitter and its resource envelopes

The emitter *program* is schedule free — `BankEmittedAtomLoop.inverseBankEmitterProgram`
is one `linkPrograms` of the given adapter with the fixed atom-emitter loop, and
carries no schedule numeral — so it is reused verbatim under a fixed-side name.
Only its two envelopes are schedule indexed. -/

/-! ## 9. The emitter premise, discharged -/

/-! ## 10. `bodyRun` from the presentation and the compiler's run -/

end NearCubicWires.FixedScheduleAtomLoop
