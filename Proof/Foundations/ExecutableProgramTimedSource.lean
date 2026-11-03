import Proof.Foundations.ExecutableInterfaces

/-!
# Receipt-backed executable hierarchy sources

`TimedDecisionMachine` is retained as a legacy semantic view only.  At the
source boundary, one fixed `ExecutableLanguageProgram` determines both
acceptance and the charged step budget.  The receipt theorem below ties that
budget to the actual interpreter invocation.

The projection-PCP guarantee is deliberately quantified over executable
programs rather than arbitrary pairs of semantic acceptance and step
functions.  Results still project to the existing executable and semantic PCP
views, so internal consumers do not need a second PCP representation.
-/

namespace NearCubicWires.ExecutableProgramTimedSource

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

def programSteps
    (program : ExecutableLanguageProgram) (n : ℕ) (input : BitInput n) : ℕ :=
  program.runner.budget (program.request input)

/-- The only permitted timed view of an executable hierarchy program. -/
def toTimedDecisionMachine
    (program : ExecutableLanguageProgram) : TimedDecisionMachine where
  accepts := program.language
  steps := programSteps program

@[simp] theorem toTimedDecisionMachine_accepts
    (program : ExecutableLanguageProgram) (n : ℕ) (input : BitInput n) :
    (toTimedDecisionMachine program).accepts n input = program.language n input :=
  rfl

@[simp] theorem toTimedDecisionMachine_steps
    (program : ExecutableLanguageProgram) (n : ℕ) (input : BitInput n) :
    (toTimedDecisionMachine program).steps n input =
      program.runner.budget (program.request input) :=
  rfl


end NearCubicWires.ExecutableProgramTimedSource
