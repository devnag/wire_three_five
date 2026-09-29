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

/-- A refuter source whose hierarchy is carried by one fixed executable
program.  Every reference to the hierarchy language below is definitionally
the output language of that program. -/
structure ExecutableProgramRefuterSource (bound : ℕ → ℕ) where
  hierarchyProgram : ExecutableLanguageProgram
  hierarchySteps : ∀ n input, programSteps hierarchyProgram n input ≤ bound n
  refuter : ExecutableSATOracleRefuter hierarchyProgram.language bound
  sound : ∀ machine : ExecutableWeakNondeterministicMachine,
    RunsInLittleO machine.toSemantic bound →
    (∀ n, machine.witnessBits n ≤ n / 10) →
    ∃ onset, ∀ n, onset ≤ n →
      (machine.toSemantic.accepts (refuter.output machine n) ↔
        hierarchyProgram.language n (refuter.output machine n) = false)

def ExecutableProgramRefuterSource.hierarchyMachine
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    TimedDecisionMachine :=
  toTimedDecisionMachine source.hierarchyProgram

/-- Exact compatibility adapter for the large legacy recovery cone.  Its
timed machine is derived from `hierarchyProgram`; no arbitrary step callback
is introduced by this projection. -/
def ExecutableProgramRefuterSource.toLegacy
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    ExecutableRefuterSource bound where
  hierarchyMachine := source.hierarchyMachine
  hierarchySteps := source.hierarchySteps
  refuter := source.refuter
  sound := source.sound

@[simp] theorem ExecutableProgramRefuterSource.toLegacy_hierarchyMachine
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    source.toLegacy.hierarchyMachine =
      toTimedDecisionMachine source.hierarchyProgram :=
  rfl

@[simp] theorem ExecutableProgramRefuterSource.toLegacy_refuter
    {bound : ℕ → ℕ} (source : ExecutableProgramRefuterSource bound) :
    source.toLegacy.refuter = source.refuter :=
  rfl


end NearCubicWires.ExecutableProgramTimedSource
