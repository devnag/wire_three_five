import Mathlib
import Proof.Foundations.AppendixC
import Proof.Foundations.ExecutableInterfaces
import Proof.Foundations.ThresholdCompiler

/-!
# Executable Appendix-C recovery pipeline

This module isolates the reusable transfer objects between the published
source interfaces and the concrete headline circuit bounds.  Closed source
assembly lives downstream; this file does not export a caller-supplied
composition, branch-builder, or headline premise.

The machine lemmas are deliberately about `runNPOracleProgram` itself.  In
particular, a semantic language evaluator or a runtime number unattached to an
execution trace cannot be promoted to `InENP`.
-/

namespace NearCubicWires.RecoveryPipeline

open NearCubicWires
open NearCubicWires.AppendixC
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.SourceInterfaces

/-! ## Exponential absorption -/

/-- Number of exponent bits needed to absorb a fixed multiplicative
coefficient into the canonical `2^(O(n))` machine budget. -/
def coefficientExponent (coefficient : ℕ) : ℕ :=
  Nat.log 2 coefficient + 1

theorem coefficient_le_two_pow (coefficient : ℕ) :
    coefficient ≤ 2 ^ coefficientExponent coefficient := by
  exact Nat.le_of_lt (by
    simpa [coefficientExponent, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by omega : 1 < 2) coefficient))

/-! ## Fixed refuter dichotomy -/

/-! ## XOR and Case-1 amplification into one per-core type -/

/-- Concrete average-case hardness at one arity and one size cap. -/
def AverageHardAt (family : SizedFunctionFamily) {n : ℕ}
    (function : BoolFunction n) (size : ℕ) (advantage : ℝ) : Prop :=
  ∀ candidate : BoolFunction n, family n candidate size →
    agreement candidate function ≤ 1 / 2 + advantage

/-- Ordinary fan-in-two circuits embedded into the common semantic family used
by the XOR source theorem. -/
def booleanCircuitFamily : SizedFunctionFamily :=
  fun n function size =>
    ∃ circuit : BooleanCircuit n,
      circuit.size ≤ size ∧ circuit.eval = function

/-- A per-core result records only one function, cap, and advantage.  It does
not quantify over all large lengths and is therefore strictly below either
headline theorem. -/
structure HardCore (family : SizedFunctionFamily) where
  arity : ℕ
  function : BoolFunction arity
  size : ℕ
  advantage : ℝ
  hard : AverageHardAt family function size advantage

/-- Explicit fixed executable algorithm and constants extracted from the
strengthened STV source contract. -/
structure AmplifierWitness where
  algorithm : ExecutableWorstCaseAmplifierAlgorithm
  stvExponent : ℕ
  arityCoefficient : ℕ
  stvExponentPositive : 1 ≤ stvExponent
  arityCoefficientPositive : 1 ≤ arityCoefficient
  sound : ∀ (sizeBound : ℕ → ℕ), TimeConstructible sizeBound →
    ∀ (n : ℕ) (function : BoolFunction n),
      WorstCaseHardAt function (sizeBound n) →
      let output := algorithm.amplify n function
      output.outputArity ≤ arityCoefficient * n ∧
        (∀ circuit : BooleanCircuit output.outputArity,
          circuit.size ≤ integerFloorRoot stvExponent (sizeBound n) →
          agreement circuit.eval output.function ≤
            1 / 2 + Real.rpow (sizeBound n : ℝ)
              (-(1 : ℝ) / stvExponent))

structure CaseOneInput (witness : AmplifierWitness) where
  sizeBound : ℕ → ℕ
  constructible : TimeConstructible sizeBound
  seedArity : ℕ
  seed : BoolFunction seedArity
  worstCaseHard : WorstCaseHardAt seed (sizeBound seedArity)

noncomputable def hardCoreFromCaseOne
    {witness : AmplifierWitness} (input : CaseOneInput witness) :
    HardCore booleanCircuitFamily := by
  let output := witness.algorithm.amplify input.seedArity input.seed
  refine
    { arity := output.outputArity
      function := output.function
      size := integerFloorRoot witness.stvExponent
        (input.sizeBound input.seedArity)
      advantage := Real.rpow (input.sizeBound input.seedArity : ℝ)
        (-(1 : ℝ) / witness.stvExponent)
      hard := ?_ }
  intro candidate hcandidate
  rcases hcandidate with ⟨circuit, hsize, heval⟩
  subst candidate
  exact
    (witness.sound input.sizeBound input.constructible
      input.seedArity input.seed input.worstCaseHard).2 circuit hsize

/-! ## Bounded-jump scheduling and exact padding -/

def finSplitEquiv {core target : ℕ} (hcore : core ≤ target) :
    Fin core ⊕ Fin (target - core) ≃ Fin target :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le hcore))

/-- Pad a core truth table by ignoring the right summand of a canonical split
of the target coordinates. -/
def padCore {core target : ℕ} (function : BoolFunction core)
    (hcore : core ≤ target) : BoolFunction target :=
  fun input =>
    function fun index => input (finSplitEquiv hcore (.inl index))

/-- Fix all non-core coordinates of a target truth table. -/
def restrictTarget {core target : ℕ} (function : BoolFunction target)
    (hcore : core ≤ target) (padding : BitInput (target - core)) :
    BoolFunction core :=
  fun input =>
    function fun index =>
      Sum.elim input padding ((finSplitEquiv hcore).symm index)

end NearCubicWires.RecoveryPipeline
