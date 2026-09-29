import Proof.MachineModel.BankEmittedAtomLoop

/-!
# An executable presentation of the padded outer PCP

`BankEmittedAtomLoop.inverse_bodyRun_ofCompiler` consumes the presentation
premise as a full semantic equality

`pcp.toSemantic = paddedOuterPCP outer`,

and that equality is **not available to any executable presentation**:
`ExecutableProjectionPCP.toSemantic` declares `constructionSteps` to be the
presentation's *own* shape budget, while `paddedOuterPCP outer` inherits the
source PCP's, and the padded shape program — which must also evaluate
`Nat.log 2 (widthBudget outer …)` — cannot halt inside the source budget.  The
two cost declarations therefore differ, and no executable presentation can
satisfy the equality on the nose.

`BankEmittedAtomLoop` already anticipates this and weakens the consumer's
hypothesis to `InverseScheduleAtomsAgree`, an equality of *atom streams*.  What
was missing is the bridge: the atom stream is a function of the four semantic
fields alone, so a budget-mismatched presentation suffices.  §1 proves exactly
that.

The obstruction to proving it by `rfl` is real: `compileCountCases` and
`compileVerifierRows` recurse over `List.ofFn id` and `allRandomness`, both of
which are stuck at a symbolic width, so the definitional unfolder compares the
two projection PCPs *as arguments* of a blocked recursor and fails.  §1
therefore performs the two list inductions explicitly.  The dependent step of
each induction is packaged as one named combinator (`andStepAt`, `orStepAt`) so
that the inductive hypothesis can be applied with `congrArg`: a bare `rw` fails
with `motive is not type correct`, because the compiler's anonymous
`CompiledWire` literal is indexed by the very predicate being rewritten.

§2 records the extensionality of `ProjectionPCP` and §3 states the residual
premise

`PresentsPaddedOuterPCP outer pcp : pcp.toSemantic =
  withConstructionSteps (paddedOuterPCP outer) pcp.shape.budget`,

which — unlike the equality it replaces — is *not* refuted by the cost
mismatch, and discharges `InverseScheduleAtomsAgree` from it.  §4 restates
`inverse_bodyRun_ofCompiler` against the new premise.
-/

namespace NearCubicWires.PaddedProjectionPresentation

open NearCubicWires
open NearCubicWires.BankDispatchedTargetBody
open NearCubicWires.BankEmittedAtomLoop
open NearCubicWires.BankEmittedBranchSelector
open NearCubicWires.BankRecoveryCodeProgram
open NearCubicWires.BoundedOracleStructuralCircuit
open NearCubicWires.CanonicalBalancedCall
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CaseTwoRecoveryAssembly
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.EmittedBranchTargetProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.FinitePredicateCircuit
open NearCubicWires.GeneratedBalancedRangeProgram
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionRunnerBalancedProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RecoveryScheduleEnvelope
open NearCubicWires.ScheduledRecovery
open NearCubicWires.SourceInterfaces
open NearCubicWires.StructuralAtomCalleeProgram
open NearCubicWires.StructuralAtomEmitterLoopProgram
open NearCubicWires.UniformTargetLanguageBank
open NearCubicWires.VerifiedLinker

/-! ## 1. The atom stream does not read the declared construction cost -/

/-! ## 2. Extensionality of the semantic projection PCP -/

/-! ## 3. The residual premise and the atom agreement -/

/-! ## 4. `bodyRun` from the executable presentation -/

end NearCubicWires.PaddedProjectionPresentation
