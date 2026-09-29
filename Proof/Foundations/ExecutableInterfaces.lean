import Proof.Foundations.QuotientBudgetCurrency
import Proof.Foundations.SourceInterfaces

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

/-- **The quotient-budget program carrier**.  Same field names as `PolynomialNatProgram` plus `logPower`,
so every `verifier.<field>` projection site keeps its spelling; only the
budget currency changes: `⌊coefficient·(m+1)^degree / L(m)^logPower⌋`.
`savingFits` keeps the floored budget positive — the saving divisor never
exceeds the whole budget. -/
structure QuotientNatProgram (Request : Type)
    (inputLength requestCode measure : Request → ℕ) where
  program : NPOracleProgram
  coefficient : ℕ
  coefficientPositive : 0 < coefficient
  degree : ℕ
  logPower : ℕ
  savingFits : ∀ request,
    logScale (measure request) ^ logPower ≤
      coefficient * (measure request + 1) ^ degree
  initialBitsFit : ∀ request,
    natBitLength (max (inputLength request) (requestCode request)) ≤
      quotientBudget coefficient degree logPower (measure request)
  halts : ∀ request, ∃ output,
    runNPOracleProgram program
      (quotientBudget coefficient degree logPower (measure request))
      (quotientBudget coefficient degree logPower (measure request))
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some output

def QuotientNatProgram.budget {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  quotientBudget runner.coefficient runner.degree runner.logPower
    (measure request)

theorem QuotientNatProgram.budget_pos {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) : 0 < runner.budget request :=
  Nat.div_pos (runner.savingFits request)
    (pow_pos (Nat.clog_pos (by norm_num) (by omega)) _)

def QuotientNatProgram.toBounded {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure) :
    BoundedNatProgram Request inputLength requestCode where
  program := runner.program
  fuel := runner.budget
  registerBits := runner.budget
  fuelPositive := runner.budget_pos
  registerBitsPositive := runner.budget_pos
  initialBitsFit := runner.initialBitsFit

def QuotientNatProgram.execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) : ℕ :=
  runner.toBounded.execute request

theorem QuotientNatProgram.run_eq_execute {Request : Type}
    {inputLength requestCode measure : Request → ℕ}
    (runner : QuotientNatProgram Request inputLength requestCode measure)
    (request : Request) :
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState (inputLength request) (requestCode request)) =
        some (runner.execute request) := by
  obtain ⟨output, houtput⟩ := runner.halts request
  simp [QuotientNatProgram.budget, QuotientNatProgram.execute,
    QuotientNatProgram.toBounded, BoundedNatProgram.execute, houtput]

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


def encodeBoolFunction {n : ℕ} (function : BoolFunction n) : ℕ :=
  encodeBoolList (boolFunctionTable function)



def encodeNPOracleInstruction : NPOracleInstruction → ℕ
  | .halt output => Nat.pair 0 output
  | .set register value next =>
      Nat.pair 1 (Nat.pair register (Nat.pair value next))
  | .copy source destination next =>
      Nat.pair 2 (Nat.pair source (Nat.pair destination next))
  | .increment register next => Nat.pair 3 (Nat.pair register next)
  | .decrement register next => Nat.pair 11 (Nat.pair register next)
  | .pair left right destination next =>
      Nat.pair 4 (Nat.pair left (Nat.pair right (Nat.pair destination next)))
  | .unpairLeft source destination next =>
      Nat.pair 5 (Nat.pair source (Nat.pair destination next))
  | .unpairRight source destination next =>
      Nat.pair 6 (Nat.pair source (Nat.pair destination next))
  | .branchZero register zeroTarget nonzeroTarget =>
      Nat.pair 7 (Nat.pair register (Nat.pair zeroTarget nonzeroTarget))
  | .sat query destination next =>
      Nat.pair 8 (Nat.pair query (Nat.pair destination next))
  | .encodeNat source destination next =>
      Nat.pair 9 (Nat.pair source (Nat.pair destination next))
  | .shiftRight source amount destination next =>
      Nat.pair 10
        (Nat.pair source (Nat.pair amount (Nat.pair destination next)))
  | .testBit source index destination next =>
      Nat.pair 12
        (Nat.pair source (Nat.pair index (Nat.pair destination next)))
  | .add left right destination next =>
      Nat.pair 13
        (Nat.pair left (Nat.pair right (Nat.pair destination next)))
  | .subtract left right destination next =>
      Nat.pair 14
        (Nat.pair left (Nat.pair right (Nat.pair destination next)))
  | .shiftLeft source amount destination next =>
      Nat.pair 15
        (Nat.pair source (Nat.pair amount (Nat.pair destination next)))

def encodeNPOracleProgram (program : NPOracleProgram) : ℕ :=
  Encodable.encode (program.map encodeNPOracleInstruction)

/-! ## Executable refinements of finite algorithms -/

structure ExactDecompositionRequest where
  arity : ℕ
  gate : NormalizedThresholdGate arity

structure RectangularProductRequest where
  dimension : ℕ
  left : BitMatrix dimension (rectangularInnerDimension dimension)
  right : BitMatrix (rectangularInnerDimension dimension) dimension

/-! ## Projection PCP: construction and every queried coordinate are executable -/

def decodeProjectedRandomBit (width code : ℕ) : ProjectedRandomBit width :=
  let tagAndIndex := Nat.unpair code
  if hwidth : width = 0 then
    .constant (tagAndIndex.2.testBit 0)
  else
    let index : Fin width :=
      ⟨tagAndIndex.2 % width, Nat.mod_lt _ (Nat.pos_of_ne_zero hwidth)⟩
    if tagAndIndex.1 % 3 = 0 then .bit index
    else if tagAndIndex.1 % 3 = 1 then .negatedBit index
    else .constant (tagAndIndex.2.testBit 0)

def decodeLiteral {arity : ℕ} (arityPositive : 0 < arity)
    (code : ℕ) : Literal arity :=
  let tagAndIndex := Nat.unpair code
  let index : Fin arity :=
    ⟨tagAndIndex.2 % arity, Nat.mod_lt _ arityPositive⟩
  if tagAndIndex.1 % 2 = 0 then .positive index else .negative index

def decodeThreeCNF (arity code : ℕ) : ThreeCNF arity :=
  if harity : 0 < arity then
    let raw := (Encodable.decode code : Option (List (List ℕ))).getD []
    { clauses := raw.map fun clause index =>
        decodeLiteral harity (clause.getD index.val 0) }
  else
    { clauses := [] }

structure ProjectionQueryRequest where
  inputArity : ℕ
  width : ℕ
  count : ℕ
  input : BitInput inputArity
  query : Fin count
  bit : Fin width

def ProjectionQueryRequest.length (request : ProjectionQueryRequest) : ℕ :=
  request.inputArity

def ProjectionQueryRequest.code (request : ProjectionQueryRequest) : ℕ :=
  Nat.pair request.inputArity (Nat.pair (encodeBitInput request.input)
    (Nat.pair request.query.val request.bit.val))

def ProjectionQueryRequest.measure (request : ProjectionQueryRequest) : ℕ :=
  request.inputArity + request.width + request.count

structure ProjectionDecisionRequest where
  inputArity : ℕ
  width : ℕ
  count : ℕ
  input : BitInput inputArity
  randomness : BitInput width

def ProjectionDecisionRequest.length (request : ProjectionDecisionRequest) : ℕ :=
  request.inputArity

def ProjectionDecisionRequest.code (request : ProjectionDecisionRequest) : ℕ :=
  Nat.pair request.inputArity
    (Nat.pair (encodeBitInput request.input)
      (encodeBitInput request.randomness))

def ProjectionDecisionRequest.measure (request : ProjectionDecisionRequest) : ℕ :=
  request.inputArity + request.width + request.count

structure ExecutableProjectionPCP (machine : TimedDecisionMachine)
    (timeBound : ℕ → ℕ) where
  shape : PolynomialNatProgram ℕ id id
    (fun n => n + logScale (timeBound n))
  shapeOracleFree : OracleFree shape.program
  query : PolynomialNatProgram ProjectionQueryRequest
    ProjectionQueryRequest.length ProjectionQueryRequest.code
    ProjectionQueryRequest.measure
  queryOracleFree : OracleFree query.program
  decisionRunner : PolynomialNatProgram ProjectionDecisionRequest
    ProjectionDecisionRequest.length ProjectionDecisionRequest.code
    ProjectionDecisionRequest.measure
  decisionOracleFree : OracleFree decisionRunner.program

def ExecutableProjectionPCP.shapeCode {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ExecutableProjectionPCP machine timeBound)
    (n : ℕ) : ℕ :=
  pcp.shape.execute n

def ExecutableProjectionPCP.nativeWidth {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ExecutableProjectionPCP machine timeBound)
    (n : ℕ) : ℕ :=
  (Nat.unpair (pcp.shapeCode n)).1

def ExecutableProjectionPCP.queryCount {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ExecutableProjectionPCP machine timeBound)
    (n : ℕ) : ℕ :=
  (Nat.unpair (pcp.shapeCode n)).2

def ExecutableProjectionPCP.queryRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) : ProjectionQueryRequest :=
  ⟨n, pcp.nativeWidth n, pcp.queryCount n, input, query, bit⟩

def ExecutableProjectionPCP.queryAddressBits
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (query : Fin (pcp.queryCount n))
    (bit : Fin (pcp.nativeWidth n)) :
    ProjectedRandomBit (pcp.nativeWidth n) :=
  let outputCode := pcp.query.execute (pcp.queryRequest input query bit)
  decodeProjectedRandomBit (pcp.nativeWidth n) outputCode

def ExecutableProjectionPCP.decisionRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) :
    ProjectionDecisionRequest :=
  ⟨n, pcp.nativeWidth n, pcp.queryCount n, input, randomness⟩

def ExecutableProjectionPCP.decision
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n)) :
    ThreeCNF (pcp.queryCount n) :=
  let outputCode :=
    pcp.decisionRunner.execute (pcp.decisionRequest input randomness)
  decodeThreeCNF (pcp.queryCount n) outputCode

def ExecutableProjectionPCP.toSemantic
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) :
    ProjectionPCP machine timeBound where
  nativeWidth := pcp.nativeWidth
  queryCount := pcp.queryCount
  queryAddressBits := pcp.queryAddressBits
  decision := pcp.decision
  constructionSteps := pcp.shape.budget

@[simp] theorem ExecutableProjectionPCP.toSemantic_nativeWidth
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) :
    pcp.toSemantic.nativeWidth n = pcp.nativeWidth n := rfl

@[simp] theorem ExecutableProjectionPCP.toSemantic_queryCount
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) (n : ℕ) :
    pcp.toSemantic.queryCount n = pcp.queryCount n := rfl

/-- The source PCP's compact substitution receives one fixed input and a
candidate oracle circuit.  The charged measure includes every variable-sized
part of the request; in particular, the oracle is charged by DAG size. -/
structure ProjectionSubstitutionRequest
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) where
  inputArity : ℕ
  input : BitInput inputArity
  oracle : BooleanCircuit (pcp.nativeWidth inputArity)

def ProjectionSubstitutionRequest.length
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (request : ProjectionSubstitutionRequest pcp) : ℕ :=
  request.inputArity

def ProjectionSubstitutionRequest.code
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (request : ProjectionSubstitutionRequest pcp) : ℕ :=
  Nat.pair request.inputArity
    (Nat.pair (encodeBitInput request.input)
      (encodeBooleanCircuit request.oracle))

def ProjectionSubstitutionRequest.measure
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    {pcp : ExecutableProjectionPCP machine timeBound}
    (request : ProjectionSubstitutionRequest pcp) : ℕ :=
  request.inputArity + pcp.nativeWidth request.inputArity + request.oracle.size

/-- Executable compact substitution for the outer PCP verifier.  `computes`
ties the reported circuit to the actual interpreter output, while `equivalent`
states its pointwise verifier semantics; neither field imports a hardness or
recovery conclusion. -/
structure ExecutableProjectionSubstitution
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ExecutableProjectionPCP machine timeBound) where
  circuit : (request : ProjectionSubstitutionRequest pcp) →
    BooleanCircuit (pcp.nativeWidth request.inputArity)
  runner : PolynomialNatProgram (ProjectionSubstitutionRequest pcp)
    ProjectionSubstitutionRequest.length
    ProjectionSubstitutionRequest.code
    ProjectionSubstitutionRequest.measure
  runnerOracleFree : OracleFree runner.program
  computes : ∀ request,
    runNPOracleProgram runner.program (runner.budget request)
      (runner.budget request)
      (initialNPOracleState request.inputArity
        (ProjectionSubstitutionRequest.code request)) =
      some (encodeBooleanCircuit (circuit request))
  equivalent : ∀ request randomness,
    (circuit request).eval randomness =
      (pcp.decision request.input randomness).eval fun query =>
        request.oracle.eval fun bit =>
          (pcp.queryAddressBits request.input query bit).eval randomness
  sizeCoefficient : ℕ
  sizeCoefficientPositive : 0 < sizeCoefficient

/-! ## Pointwise PCPP: shape, clauses, supports, and honest words are executable -/

/-! ## Executable weak machines and the SAT-oracle refuter -/

structure WeakVerifierRequest where
  inputArity : ℕ
  witnessArity : ℕ
  input : BitInput inputArity
  witness : BitInput witnessArity

def WeakVerifierRequest.length (request : WeakVerifierRequest) : ℕ :=
  request.inputArity

def WeakVerifierRequest.code (request : WeakVerifierRequest) : ℕ :=
  Nat.pair request.inputArity
    (Nat.pair (encodeBitInput request.input) (encodeBitInput request.witness))

def WeakVerifierRequest.measure (request : WeakVerifierRequest) : ℕ :=
  request.inputArity + request.witnessArity

/-- The machine's verifier and witness-length function are both interpreter
programs.  Its semantic `run` and `steps` fields below are derived, not stored. -/
structure ExecutableWeakNondeterministicMachine where
  witnessShape : PolynomialNatProgram ℕ id id id
  witnessShapeOracleFree : OracleFree witnessShape.program
  verifier : QuotientNatProgram WeakVerifierRequest
    WeakVerifierRequest.length WeakVerifierRequest.code WeakVerifierRequest.measure
  verifierOracleFree : OracleFree verifier.program

def ExecutableWeakNondeterministicMachine.witnessBits
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : ℕ :=
  machine.witnessShape.execute n

def ExecutableWeakNondeterministicMachine.verifierBudget
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : ℕ :=
  machine.verifier.budget
    { inputArity := n
      witnessArity := machine.witnessBits n
      input := fun _ => false
      witness := fun _ => false }

def ExecutableWeakNondeterministicMachine.verifierRequest
    (machine : ExecutableWeakNondeterministicMachine) {n : ℕ}
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) :
    WeakVerifierRequest :=
  ⟨n, machine.witnessBits n, input, witness⟩

def ExecutableWeakNondeterministicMachine.run
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ)
    (input : BitInput n) (witness : BitInput (machine.witnessBits n)) : Bool :=
  let outputCode :=
    machine.verifier.execute (machine.verifierRequest input witness)
  outputCode != 0

def ExecutableWeakNondeterministicMachine.toSemantic
    (machine : ExecutableWeakNondeterministicMachine) :
    WeakNondeterministicMachine where
  witnessBits := machine.witnessBits
  run := machine.run
  steps := fun n _ _ => machine.verifierBudget n

def ExecutableWeakNondeterministicMachine.description
    (machine : ExecutableWeakNondeterministicMachine) : ℕ :=
  Nat.pair (encodeNPOracleProgram machine.witnessShape.program)
    (Nat.pair machine.witnessShape.coefficient
      (Nat.pair machine.witnessShape.degree
        (Nat.pair (encodeNPOracleProgram machine.verifier.program)
          (Nat.pair machine.verifier.coefficient
            (Nat.pair machine.verifier.degree machine.verifier.logPower)))))

structure RefuterRequest where
  inputArity : ℕ
  machineDescription : ℕ
  boundValue : ℕ

def RefuterRequest.length (request : RefuterRequest) : ℕ :=
  request.inputArity

def RefuterRequest.code (request : RefuterRequest) : ℕ :=
  Nat.pair request.machineDescription request.inputArity

def RefuterRequest.measure (request : RefuterRequest) : ℕ :=
  request.boundValue

structure ExecutableSATOracleRefuter (hierarchy : Language)
    (bound : ℕ → ℕ) where
  runner : PolynomialNatProgram RefuterRequest
    RefuterRequest.length RefuterRequest.code RefuterRequest.measure

def ExecutableSATOracleRefuter.request {hierarchy : Language}
    {bound : ℕ → ℕ} (_refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) :
    RefuterRequest :=
  ⟨n, machine.description, bound n⟩

def ExecutableSATOracleRefuter.outputCode {hierarchy : Language}
    {bound : ℕ → ℕ} (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : ℕ :=
  refuter.runner.execute (refuter.request machine n)

def ExecutableSATOracleRefuter.output {hierarchy : Language}
    {bound : ℕ → ℕ} (refuter : ExecutableSATOracleRefuter hierarchy bound)
    (machine : ExecutableWeakNondeterministicMachine) (n : ℕ) : BitInput n :=
  fun index => (refuter.outputCode machine n).testBit index.val

/-- The refuter's hierarchy is supplied with the actual timed machine consumed
by the projection-PCP theorem.  Making the language definitionally equal to
that machine's acceptance function prevents a caller from attaching a
fabricated step counter to an arbitrary language. -/
structure ExecutableRefuterSource (bound : ℕ → ℕ) where
  hierarchyMachine : TimedDecisionMachine
  hierarchySteps :
    ∀ n input, hierarchyMachine.steps n input ≤ bound n
  refuter : ExecutableSATOracleRefuter hierarchyMachine.accepts bound
  sound : ∀ machine : ExecutableWeakNondeterministicMachine,
    RunsInLittleO machine.toSemantic bound →
    (∀ n, machine.witnessBits n ≤ n / 10) →
    ∃ onset, ∀ n, onset ≤ n →
      (machine.toSemantic.accepts (refuter.output machine n) ↔
        hierarchyMachine.accepts n (refuter.output machine n) = false)

/-! ## Worst-case amplification with an executable constructor and evaluator -/


def AmplifierRequest.length (request : AmplifierRequest) : ℕ :=
  request.inputArity

def AmplifierRequest.code (request : AmplifierRequest) : ℕ :=
  Nat.pair request.inputArity (encodeBoolFunction request.function)

def AmplifierRequest.measure (request : AmplifierRequest) : ℕ :=
  request.inputArity

structure AmplifierEvaluationRequest where
  outputArity : ℕ
  descriptor : ℕ
  input : BitInput outputArity

def AmplifierEvaluationRequest.length
    (request : AmplifierEvaluationRequest) : ℕ :=
  request.outputArity

def AmplifierEvaluationRequest.code
    (request : AmplifierEvaluationRequest) : ℕ :=
  Nat.pair request.descriptor (encodeBitInput request.input)

def AmplifierEvaluationRequest.measure
    (request : AmplifierEvaluationRequest) : ℕ :=
  request.outputArity

/-- The construction program returns `(outputArity, descriptor)`.  The second
program evaluates that descriptor, so the amplified truth table is not stored
as an arbitrary Lean function. -/
structure ExecutableWorstCaseAmplifierAlgorithm where
  construction : ExponentialNatProgram AmplifierRequest
    AmplifierRequest.length AmplifierRequest.code AmplifierRequest.measure
  constructionOracleFree : OracleFree construction.program
  evaluator : PolynomialNatProgram AmplifierEvaluationRequest
    AmplifierEvaluationRequest.length AmplifierEvaluationRequest.code
    AmplifierEvaluationRequest.measure
  evaluatorOracleFree : OracleFree evaluator.program

def ExecutableWorstCaseAmplifierAlgorithm.constructionCode
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) : ℕ :=
  algorithm.construction.execute request

def ExecutableWorstCaseAmplifierAlgorithm.outputArity
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) : ℕ :=
  (Nat.unpair (algorithm.constructionCode request)).1

def ExecutableWorstCaseAmplifierAlgorithm.descriptor
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) : ℕ :=
  (Nat.unpair (algorithm.constructionCode request)).2

def ExecutableWorstCaseAmplifierAlgorithm.outputFunction
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (request : AmplifierRequest) :
    BoolFunction (algorithm.outputArity request) :=
  fun input =>
    let evaluationRequest : AmplifierEvaluationRequest :=
      ⟨algorithm.outputArity request, algorithm.descriptor request, input⟩
    let outputCode := algorithm.evaluator.execute evaluationRequest
    outputCode != 0

def ExecutableWorstCaseAmplifierAlgorithm.amplify
    (algorithm : ExecutableWorstCaseAmplifierAlgorithm)
    (n : ℕ) (function : BoolFunction n) : AmplifiedTruthTable n :=
  let request : AmplifierRequest := ⟨n, function⟩
  { outputArity := algorithm.outputArity request
    function := algorithm.outputFunction request
    constructionSteps := algorithm.construction.budget request }

end NearCubicWires.ExecutableInterfaces
