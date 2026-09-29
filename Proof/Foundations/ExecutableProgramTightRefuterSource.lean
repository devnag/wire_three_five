import Proof.Foundations.ExecutableProgramTimedSource

/-!
# Certified-tight refuter source over an executable hierarchy program

This module combines two fidelity corrections: verifier time is bounded above
by a literal interpreter receipt, and the refuter's hierarchy language/time
pair is derived from one `ExecutableLanguageProgram`.
-/

namespace NearCubicWires.ExecutableProgramTightRefuterSource

open NearCubicWires
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.ExecutableProgramTimedSource
open NearCubicWires.SourceInterfaces

/-- Request-indexed resources for the exact verifier program.  The advertised
semantic charge dominates both resources used by the literal halting receipt. -/
structure ReceiptBackedTightVerifierBudget
    (machine : ExecutableWeakNondeterministicMachine) where
  fuel : WeakVerifierRequest → ℕ
  registerBits : WeakVerifierRequest → ℕ
  advertisedSteps : WeakVerifierRequest → ℕ
  fuelPositive : ∀ request, 0 < fuel request
  registerBitsPositive : ∀ request, 0 < registerBits request
  fuel_le_advertisedSteps : ∀ request, fuel request ≤ advertisedSteps request
  registerBits_le_advertisedSteps : ∀ request,
    registerBits request ≤ advertisedSteps request
  initialBitsFit : ∀ request,
    natBitLength (max request.length request.code) ≤ registerBits request
  halts : ∀ request,
    runNPOracleProgram machine.verifier.program (registerBits request)
        (fuel request)
        (initialNPOracleState request.length request.code) =
      some (machine.verifier.execute request)

structure ReceiptBackedTightWeakMachine where
  legacy : ExecutableWeakNondeterministicMachine
  receipt : ReceiptBackedTightVerifierBudget legacy

def ReceiptBackedTightWeakMachine.witnessBits
    (machine : ReceiptBackedTightWeakMachine) (n : ℕ) : ℕ :=
  machine.legacy.witnessBits n

def ReceiptBackedTightWeakMachine.verifierRequest
    (machine : ReceiptBackedTightWeakMachine) {n : ℕ}
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) :
    WeakVerifierRequest :=
  machine.legacy.verifierRequest input witness

def ReceiptBackedTightWeakMachine.execute
    (machine : ReceiptBackedTightWeakMachine)
    (request : WeakVerifierRequest) : ℕ :=
  (runNPOracleProgram machine.legacy.verifier.program
      (machine.receipt.registerBits request) (machine.receipt.fuel request)
      (initialNPOracleState request.length request.code)).getD 0

def ReceiptBackedTightWeakMachine.run
    (machine : ReceiptBackedTightWeakMachine) (n : ℕ)
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) : Bool :=
  machine.execute (machine.verifierRequest input witness) != 0

def ReceiptBackedTightWeakMachine.toSemantic
    (machine : ReceiptBackedTightWeakMachine) : WeakNondeterministicMachine where
  witnessBits := machine.witnessBits
  run := machine.run
  steps := fun _n input witness =>
    machine.receipt.advertisedSteps (machine.verifierRequest input witness)

/-- Coarse legacy programs embed without changing their semantics.  This is
used only to derive the compatibility projection; genuinely tight consumers
use an independently constructed receipt. -/
def ReceiptBackedTightWeakMachine.ofLegacy
    (machine : ExecutableWeakNondeterministicMachine) :
    ReceiptBackedTightWeakMachine where
  legacy := machine
  receipt := {
    fuel := machine.verifier.budget
    registerBits := machine.verifier.budget
    advertisedSteps := machine.verifier.budget
    fuelPositive := by
      intro request
      exact machine.verifier.budget_pos request
    registerBitsPositive := by
      intro request
      exact machine.verifier.budget_pos request
    fuel_le_advertisedSteps := fun _ => le_rfl
    registerBits_le_advertisedSteps := fun _ => le_rfl
    initialBitsFit := machine.verifier.initialBitsFit
    halts := machine.verifier.run_eq_execute }

@[simp] theorem ReceiptBackedTightWeakMachine.ofLegacy_witnessBits
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) :
    (ReceiptBackedTightWeakMachine.ofLegacy machine).witnessBits n =
      machine.witnessBits n :=
  rfl

@[simp] theorem ReceiptBackedTightWeakMachine.ofLegacy_steps
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ)
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) :
    (ReceiptBackedTightWeakMachine.ofLegacy machine).toSemantic.steps
        n input witness = machine.toSemantic.steps n input witness :=
  rfl


end NearCubicWires.ExecutableProgramTightRefuterSource
