import Proof.Foundations.SourceCore
import Proof.Foundations.OrdinaryRewindCarrier
import Proof.Foundations.SupplierPipeline
import Proof.Foundations.OuterPCPRecovery
import Proof.Foundations.OperationalWilliamsSourceCore
import Statement

/-!
# Representation-sensitive literature interfaces

Ordinary source algorithms are retained
with literal finite-machine receipts. Locally strengthened codecs, queries,
ceil-root transport, rational resources and physical closure are separate
obligations, never additional literature fields. No legacy PublishedContracts
or impossible executable-source witness is used here.
-/
namespace NearCubicWires.RepairRepresentation

open SourceInterfaces ExecutableInterfaces RepairSource LocalBitMultitape CanonicalBinary
open SupplierPipeline RecoveryPipeline OuterPCPRecovery CompilerSemantics
open WilliamsPublishedForm
open WilliamsProductCertificate
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Conventional explicit binary words: linear sequence structure -/




def thresholdWord {n : ℕ} (g : NormalizedThresholdGate n) : List Bool :=
  natWord n ++ (List.ofFn g.weight).flatMap intWord ++ intWord g.threshold

def exactWord {n : ℕ} (g : ExactThresholdGate n) : List Bool :=
  (List.ofFn g.weight).flatMap intWord ++ intWord g.target

def exactListWord {n : ℕ} (gs : List (ExactThresholdGate n)) : List Bool :=
  natWord gs.length ++ gs.flatMap exactWord

/-! ## CW19 qualitative disjoint exact conversion

CW19 Proposition18(2): a polynomial-time explicit construction. The source
does not include AppendixA.12's repaired sharp child/coefficient envelopes.
The word format is ordinary streaming binary, not recursive Encodable lists.
-/

structure DecompositionAlgorithm where
  output : (r : ExactDecompositionRequest) → ExactDecomposition r.gate
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  constructor : OrdinaryWordFunction ExactDecompositionRequest
    (fun r => thresholdWord r.gate)
    (fun r => exactListWord (output r).children)
    (fun r => coefficient * (r.arity + r.gate.encodingBits + 1) ^ degree)

def DecompositionSource : Prop := Nonempty DecompositionAlgorithm

/-- Exact same normalized retained top used by SupplierPipeline.topDecomposition,
with only the unsupported executable wrapper removed. -/
def retainedTopDecomposition (a : DecompositionAlgorithm) {n : ℕ}
    (c : NormalizedThresholdThresholdCircuit n) :
    ExactDecomposition (nonStrictAsStrict (retainedTopGate c)) :=
  a.output ⟨c.top.support.card, nonStrictAsStrict (retainedTopGate c)⟩

theorem retainedTop_equivalent (a : DecompositionAlgorithm) {n : ℕ}
    (c : NormalizedThresholdThresholdCircuit n) (x : BitInput n) :
    c.eval x = (retainedTopDecomposition a c).children.any
      (fun child => child.eval (retainedBottomValues c x)) := by
  rw [← (retainedTopDecomposition a c).equivalent (retainedBottomValues c x)]
  rw [← retainedTopGate_eval c x]
  exact (nonStrictAsStrict_eval (retainedTopGate c) (retainedBottomValues c x)).symm

/-- The actual disjoint child-count expression, rather than a semantic OR
whose resource count has been silently substituted. -/
theorem retainedTop_count (a : DecompositionAlgorithm) {n : ℕ}
    (c : NormalizedThresholdThresholdCircuit n) (x : BitInput n) :
    ((retainedTopDecomposition a c).children.filter
      (fun child => child.eval (retainedBottomValues c x))).length = (c.eval x).toNat := by
  rw [filterLength_eq_any_toNat _ _
    ((retainedTopDecomposition a c).disjoint (retainedBottomValues c x))]
  rw [← retainedTop_equivalent]

/-! ## WilACC14: exact integer product on framed ordinary tapes

Corollaries4.4/C.2 on exact tenth powers. Ceil-root padding/cropping belongs
to the local caller. Fixed finite small cases and conventional formatting
are absorbed into the coefficient; output is on a fresh tape.
-/

structure ExactPowerRequest where
  inner : ℕ
  positive : 1 ≤ inner
  left : BitMatrix (inner ^ 10) inner
  right : BitMatrix inner (inner ^ 10)

def ExactPowerRequest.dimension (r : ExactPowerRequest) : ℕ := r.inner ^ 10

def ExactPowerRequest.output (r : ExactPowerRequest) : List Bool :=
  WilliamsLoaderForms.encodedNatCellTape
    (natBitLength r.dimension) (rowMajorNatMatrix (integerMatrixProduct r.left r.right))

structure WilliamsAlgorithm where
  tapeCount : ℕ
  stateCount : ℕ
  threeTapes : 3 ≤ tapeCount
  machine : Machine tapeCount stateCount
  outputTape : Fin tapeCount
  outputFreshLeft : outputTape.val ≠ 0
  outputFreshRight : outputTape.val ≠ 1
  coefficient : ℕ
  logExponent : ℕ
  coefficientPositive : 0 < coefficient
  runs : ∀ r : ExactPowerRequest, ∃ receipt,
    run machine (coefficient * r.dimension ^ 2 * logScale r.dimension ^ logExponent)
      (fun tape => if tape.val = 0 then
        natWord r.dimension ++ WilliamsLoaderForms.rowMajorBitMatrix r.left
       else if tape.val = 1 then
        WilliamsLoaderForms.rowMajorBitMatrix r.right
       else []) = some receipt ∧
      receipt.final.tapes outputTape = r.output

def WilliamsSource : Prop := Nonempty WilliamsAlgorithm

/-- A LOCAL ordinary wrapper for actual ceiling-dimension requests. Its
implementation loads both inputs, calls the selected source once, crops and
copies once. This record is an implementation obligation, not an import. -/
structure WilliamsCeilRealization (source : WilliamsAlgorithm) where
  coefficient : ℕ
  logExponent : ℕ
  coefficientPositive : 0 < coefficient
  sourceExponentPaid : source.logExponent ≤ logExponent
  wrapper : OrdinaryWordFunction RectangularProductRequest
    (fun r => natWord r.dimension ++
      WilliamsLoaderForms.rowMajorBitMatrix r.left ++
      WilliamsLoaderForms.rowMajorBitMatrix r.right)
    (fun r => WilliamsLoaderForms.encodedNatCellTape
      (natBitLength r.dimension) (rowMajorNatMatrix (integerMatrixProduct r.left r.right)))
    (fun r => coefficient * (r.dimension + 1) ^ 2 * (logScale r.dimension + 1) ^ logExponent)

theorem product_entry_le_inner {rows inner columns : ℕ}
    (left : BitMatrix rows inner) (right : BitMatrix inner columns)
    (row : Fin rows) (column : Fin columns) :
    integerMatrixProduct left right row column ≤ inner := by
  unfold integerMatrixProduct
  calc
    _ ≤ ∑ _i : Fin inner, 1 := by
      apply Finset.sum_le_sum
      intro i _
      split <;> omega
    _ = inner := by simp

/-! ## CLW20 Lemma3.11: typed pointwise PCPP

The small-arity qualification is necessary for half-support parity. The local
outer-width padding establishes this domain; no guarantee is projected back
to arity one. Both machines are fixed before seeing any circuit or input.
-/

structure PCPPRequest (minimumArity : ℕ) where
  arity : ℕ
  circuit : BooleanCircuit arity
  large : minimumArity ≤ arity
  sizeLarge : arity ≤ circuit.size

def pcppInput {n0 : ℕ} (r : PCPPRequest n0) : List Bool :=
  natWord r.arity ++ (encodeBooleanCircuit r.circuit).bits


def pcppOutput {n0 : ℕ} (r : PCPPRequest n0) (p : PointwisePCPP r.circuit) : List Bool :=
  natListWord [p.systematicBits, p.auxiliaryBits, p.clauseBits] ++
    (List.ofFn (fun i : Fin p.systematicBits =>
      List.ofFn (fun j : Fin r.arity => decide (j ∈ p.systematicSupport i)))).flatten ++
    natListWord ((List.ofFn fun i : Fin (2 ^ p.clauseBits) =>
      [literalIndex (p.clauses i).left, literalIndex (p.clauses i).right]).flatten)

structure PointwisePCPPAlgorithm where
  minimumArity : ℕ
  minimumArityBound : 2 ≤ minimumArity
  completeness : ℝ
  soundness : ℝ
  soundnessPositive : 0 < soundness
  gap : soundness < completeness
  completenessBelowOne : completeness < 1
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  output : (r : PCPPRequest minimumArity) → PointwisePCPP r.circuit
  systematicBound : ∀ r, (output r).systematicBits ≤ coefficient * (r.arity + 1) ^ degree
  auxiliaryBound : ∀ r, (output r).auxiliaryBits ≤ coefficient * (r.circuit.size + 1) ^ degree
  clauseCountBound : ∀ r, 2 ^ (output r).clauseBits ≤ coefficient * (r.circuit.size + 1) ^ degree
  constructor : OrdinaryWordFunction (PCPPRequest minimumArity) pcppInput
    (fun r => pcppOutput r (output r))
    (fun r => coefficient * (r.circuit.size + r.arity + 1) ^ degree)
  honest : OrdinaryWordFunction (Σ r : PCPPRequest minimumArity, BitInput r.arity)
    (fun r => pcppInput r.1 ++ List.ofFn r.2)
    (fun r => List.ofFn ((output r.1).honestAuxiliary r.2))
    (fun r => coefficient * (r.1.circuit.size + r.1.arity + 1) ^ degree)
  complete : ∀ r x, r.circuit.eval x = true →
    (output r).satisfiedFraction x ((output r).honestAuxiliary x) ≥ completeness
  sound : ∀ r x, r.circuit.eval x = false → ∀ auxiliary,
    (output r).satisfiedFraction x auxiliary ≤ soundness

def PointwisePCPPSource : Prop := Nonempty PointwisePCPPAlgorithm

def pointwiseRequest (a : PointwisePCPPAlgorithm) {n : ℕ}
    (c : BooleanCircuit n) (hn : a.minimumArity ≤ n) : PCPPRequest a.minimumArity where
  arity := n
  circuit := c.padToArity
  large := hn
  sizeLarge := BooleanCircuit.arity_le_padToArity_size c

/-- LOCAL full-object reconstruction/lookup adapters. Their requests use
actual finite output ranges. No unchecked raw code or index is admitted. -/
structure PCPPQueryRealization (a : PointwisePCPPAlgorithm) where
  coefficient : ℕ
  degree : ℕ
  coefficientPositive : 0 < coefficient
  support : OrdinaryWordFunction
    (Σ r : PCPPRequest a.minimumArity, Fin (a.output r).systematicBits)
    (fun r => pcppInput r.1 ++ natWord r.2.val)
    (fun r => List.ofFn fun j : Fin r.1.arity => decide (j ∈ (a.output r.1).systematicSupport r.2))
    (fun r => coefficient * (r.1.circuit.size + r.1.arity + 1) ^ degree)
  clause : OrdinaryWordFunction
    (Σ r : PCPPRequest a.minimumArity, Fin (2 ^ (a.output r).clauseBits))
    (fun r => pcppInput r.1 ++ natWord r.2.val)
    (fun r => natListWord [literalIndex ((a.output r.1).clauses r.2).left,
      literalIndex ((a.output r.1).clauses r.2).right])
    (fun r => coefficient * (r.1.circuit.size + r.1.arity + 1) ^ degree)

/-! ## CLW20 Lemma3.8 and its AppendixA sample/affine construction

Full literal projections and output negation are the source's typical-class
operations (PDF15/printed14). AppendixA (PDF50--52) supplies the sampled affine
form below. The rational term/mass/bit envelope and physical-wire closure are
LOCAL consequences, not strengthened fields of the literature theorem.
-/

def LiteralProjectionClosed (family : SizedFunctionFamily) : Prop :=
  ∀ {n m size : ℕ} (f : BoolFunction n), family n f size →
    ∀ p : Fin n → ProjectedRandomBit m,
      family m (fun x => f (fun i => (p i).eval x)) size

def epsilonQ (delta : ℚ) (k : ℕ) : ℚ :=
  (1 - delta) ^ (k - 1) * (1 / 2 - delta)

def alphaQ (delta : ℚ) (j : ℕ) : ℚ :=
  (1 - delta) / ((2 + delta) * epsilonQ delta j)

noncomputable def sampleCount (delta : ℚ) (n j : ℕ) : ℕ :=
  ⌈4 * (n + 1 : ℕ) / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) j ^ 2)⌉₊

inductive SampleForm (delta : ℚ) (n k : ℕ) : List (ℚ × BoolFunction n) → Prop
  | direct (f : BoolFunction n) : SampleForm delta n k [(1, f)]
  | affine (j : ℕ) (hj : 2 ≤ j) (hjk : j ≤ k)
      (atoms : List (BoolFunction n)) (hcount : atoms.length = sampleCount delta n j)
      (one : BoolFunction n) (hone : ∀ x, one x = true) :
      SampleForm delta n k
        (atoms.map (fun f => (alphaQ delta j / atoms.length, f)) ++
          [((1 - alphaQ delta j) / 2, one)])

structure SampledXorSum (family : SizedFunctionFamily) (delta : ℚ)
    (n k size : ℕ) (f : BoolFunction n) where
  sum : UnitIntervalCircuitSum family n size
  form : SampleForm delta n k sum.terms
  close : l1DistanceFromBoolean f sum.value ≤ (delta : ℝ)

def XorSource : Prop :=
  ∀ (delta : ℚ), 0 < delta → delta < 1 / 2 →
  ∀ (family : SizedFunctionFamily), LiteralProjectionClosed family →
    NegationClosedFamily family →
  ∀ {n : ℕ} (f : BoolFunction n), 1 ≤ n →
  ∀ k size, 1 ≤ k → ∀ candidate : BoolFunction (k * n),
    family (k * n) candidate size →
    1 / 2 + xorEpsilon (delta : ℝ) k < agreement candidate (xorPower f k) →
    Nonempty (SampledXorSum family delta n k size f)

noncomputable def xorTermBound (delta : ℚ) (n k : ℕ) : ℕ :=
  ⌈16 * n / ((delta : ℝ) ^ 2 * xorEpsilon (delta : ℝ) k ^ 2)⌉₊

def xorBits (delta : ℚ) (n k : ℕ) : ℕ :=
  (8 + 5 * natBitLength delta.den) * (n + k + 1)


end NearCubicWires.RepairRepresentation
