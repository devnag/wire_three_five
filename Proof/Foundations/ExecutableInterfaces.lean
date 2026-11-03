import Proof.Foundations.CanonicalBinary
import Proof.Foundations.SourceInterfaces
import Proof.Foundations.QuotientBudgetCurrency
import Statement

/-!
# Executable imported-algorithm interfaces

The published-source interfaces describe mathematical input/output behavior.
This module supplies the computational refinement used by the end-to-end
formalization: every reported output is obtained by running the fixed
`NPOracleProgram` interpreter with the displayed fuel and register-bit budget.
There is therefore no independent `steps` counter that can disagree with the
execution being certified.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.ExecutableInterfaces

open NearCubicWires
open NearCubicWires.CanonicalBinary
open NearCubicWires.SourceInterfaces

/-! ## Reusable bounded runners -/

/-- Deterministic imported algorithms may not gain power from the SAT opcode. -/
def OracleFree (program : NPOracleProgram) : Prop :=
  program.all (fun instruction => match instruction with
    | .halt _ => true
    | .set _ _ _ => true
    | .copy _ _ _ => true
    | .increment _ _ => true
    | .decrement _ _ => true
    | .add _ _ _ _ => true
    | .subtract _ _ _ _ => true
    | .pair _ _ _ _ => true
    | .unpairLeft _ _ _ => true
    | .unpairRight _ _ _ => true
    | .branchZero _ _ _ => true
    | .encodeNat _ _ _ => true
    | .shiftRight _ _ _ _ => true
    | .shiftLeft _ _ _ _ => true
    | .testBit _ _ _ _ => true
    | .sat _ _ _ => false
    ) = true

/-- A program with request-dependent, explicitly charged resources. -/
structure BoundedNatProgram (Request : Type)
    (inputLength requestCode : Request → ℕ) where
  program : NPOracleProgram
  fuel : Request → ℕ
  registerBits : Request → ℕ
  fuelPositive : ∀ request, 0 < fuel request
  registerBitsPositive : ∀ request, 0 < registerBits request
  /-- The advertised cap includes the two caller-populated registers.  The
  interpreter bounds writes, so this is the missing boundary condition that
  prevents an oversized request code from acting as free read-only advice. -/
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      registerBits request

def BoundedNatProgram.execute {Request : Type}
    {inputLength requestCode : Request → ℕ}
    (runner : BoundedNatProgram Request inputLength requestCode)
    (request : Request) : ℕ :=
  (runNPOracleProgram runner.program (runner.registerBits request)
    (runner.fuel request)
    (initialNPOracleState (inputLength request) (requestCode request))).getD 0

def polynomialBudget (coefficient degree measure : ℕ) : ℕ :=
  coefficient * (measure + 1) ^ degree

/-- Polynomial resource bounds are used as the interpreter budgets themselves. -/
structure PolynomialNatProgram (Request : Type)
    (inputLength requestCode measure : Request → ℕ) where
  program : NPOracleProgram
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  degree : ℕ
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      polynomialBudget coefficient degree (measure request)
  halts : ∀ request, ∃ output,
    runNPOracleProgram program
      (polynomialBudget coefficient degree (measure request))
      (polynomialBudget coefficient degree (measure request))
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some output

def PolynomialNatProgram.budget {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  polynomialBudget runner.coefficient runner.degree (measure request)

def PolynomialNatProgram.toBounded {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure) :
    BoundedNatProgram Request inputLength requestCode where
  program := runner.program
  fuel := runner.budget
  registerBits := runner.budget
  fuelPositive := by
    intro request
    exact Nat.mul_pos runner.coefficientPositive (pow_pos (by omega) _)
  registerBitsPositive := by
    intro request
    exact Nat.mul_pos runner.coefficientPositive (pow_pos (by omega) _)
  initialBitsFit := runner.initialBitsFit

def PolynomialNatProgram.execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : PolynomialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  runner.toBounded.execute request

def exponentialBudget (exponent measure : ℕ) : ℕ := 2 ^ (exponent * measure)

structure ExponentialNatProgram (Request : Type)
    (inputLength requestCode measure : Request → ℕ) where
  program : NPOracleProgram
  exponent : ℕ
  exponentPositive : 0 < exponent
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      exponentialBudget exponent (measure request)
  halts : ∀ request, ∃ output,
    runNPOracleProgram program
      (exponentialBudget exponent (measure request))
      (exponentialBudget exponent (measure request))
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some output

def ExponentialNatProgram.budget {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : ExponentialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  exponentialBudget runner.exponent (measure request)

def ExponentialNatProgram.toBounded {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : ExponentialNatProgram Request inputLength requestCode measure) :
    BoundedNatProgram Request inputLength requestCode where
  program := runner.program
  fuel := runner.budget
  registerBits := runner.budget
  fuelPositive := fun _ => pow_pos (by omega) _
  registerBitsPositive := fun _ => pow_pos (by omega) _
  initialBitsFit := runner.initialBitsFit

def ExponentialNatProgram.execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : ExponentialNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  runner.toBounded.execute request

/-! ## Exponential programs as total `E^NP` languages -/

/-- Canonical dependent request for evaluating one bit of a language.  The
input code is exactly the public code expected by `ENPCertificate`; the arity
already occupies interpreter register one and is not duplicated in the code. -/
structure LanguageEvaluationRequest where
  inputArity : ℕ
  input : BitInput inputArity

def LanguageEvaluationRequest.length
    (request : LanguageEvaluationRequest) : ℕ :=
  request.inputArity

def LanguageEvaluationRequest.code
    (request : LanguageEvaluationRequest) : ℕ :=
  encodeBitInput request.input

def LanguageEvaluationRequest.measure
    (request : LanguageEvaluationRequest) : ℕ :=
  max 1 request.inputArity

/-- A single exponential interpreter with a proved Boolean output.  Keeping
the output condition beside the runner rules out a semantic language path
whose values are unrelated to the certified execution trace. -/
structure ExecutableLanguageProgram where
  runner : ExponentialNatProgram LanguageEvaluationRequest
    LanguageEvaluationRequest.length LanguageEvaluationRequest.code
    LanguageEvaluationRequest.measure
  booleanOutput : ∀ request, runner.execute request ≤ 1

def ExecutableLanguageProgram.request
    (_program : ExecutableLanguageProgram)
    {n : ℕ} (input : BitInput n) : LanguageEvaluationRequest :=
  ⟨n, input⟩

def ExecutableLanguageProgram.language
    (program : ExecutableLanguageProgram) : Language :=
  fun _n input =>
    decide (program.runner.execute (program.request input) ≠ 0)

/-! ## Canonical finite encodings -/

def encodeNormalizedThresholdGate {n : ℕ}
    (gate : NormalizedThresholdGate n) : ℕ :=
  encodeTaggedList
    [encodeIntList (List.ofFn gate.weight),
      encodeInt gate.threshold]




/-! ## Executable refinements of finite algorithms -/

structure ExactDecompositionRequest where
  arity : ℕ
  gate : NormalizedThresholdGate arity

def ExactDecompositionRequest.length (request : ExactDecompositionRequest) : ℕ :=
  request.arity

def ExactDecompositionRequest.code (request : ExactDecompositionRequest) : ℕ :=
  encodeNormalizedThresholdGate request.gate

def ExactDecompositionRequest.measure (request : ExactDecompositionRequest) : ℕ :=
  request.arity + request.gate.encodingBits

def decodeExactThresholdGates (n code : ℕ) : List (ExactThresholdGate n) :=
  let raw := (Encodable.decode code : Option (List (List ℤ × ℤ))).getD []
  raw.map fun gate =>
    { weight := fun index => gate.1.getD index.val 0
      target := gate.2 }

/-- Both the output list and the resource charge are derived from one runner. -/
structure ExecutableExactDecompositionAlgorithm where
  runner : PolynomialNatProgram ExactDecompositionRequest
    ExactDecompositionRequest.length ExactDecompositionRequest.code
    ExactDecompositionRequest.measure
  oracleFree : OracleFree runner.program
  equivalent : ∀ request input,
    request.gate.strictEval input =
      (decodeExactThresholdGates request.arity
        (runner.execute request)).any (fun child => child.eval input)
  disjoint : ∀ request input,
    ((decodeExactThresholdGates request.arity
      (runner.execute request)).filter fun child => child.eval input).length ≤ 1

def ExecutableExactDecompositionAlgorithm.run
    (algorithm : ExecutableExactDecompositionAlgorithm)
    {n : ℕ} (gate : NormalizedThresholdGate n) : ExactDecomposition gate :=
  let request : ExactDecompositionRequest := ⟨n, gate⟩
  { children := decodeExactThresholdGates n (algorithm.runner.execute request)
    equivalent := algorithm.equivalent request
    disjoint := algorithm.disjoint request }

structure RectangularProductRequest where
  dimension : ℕ
  left : BitMatrix dimension (rectangularInnerDimension dimension)
  right : BitMatrix (rectangularInnerDimension dimension) dimension

/-! ## Projection PCP: construction and every queried coordinate are executable -/

/-! ## Pointwise PCPP: shape, clauses, supports, and honest words are executable -/

/-! ## Executable weak machines and the SAT-oracle refuter -/

/-! ## Worst-case amplification with an executable constructor and evaluator -/


end NearCubicWires.ExecutableInterfaces
