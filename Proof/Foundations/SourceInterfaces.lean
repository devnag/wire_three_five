import Proof.Foundations.Semantics

/-!
# Typed published-source interfaces

Each definition below is the proposition imported from one published source
row.  (There is no `source_contracts/contracts.json` in this repository; an
earlier revision of this header claimed one.  `SourceContracts.PublishedContracts`
is the registry.)  The fields quantify the mathematical objects named by the
source; no row is represented by an untyped `Prop`.  Local adapters and
quantitative strengthenings are deliberately absent.
-/

open Finset
open scoped BigOperators

namespace NearCubicWires.SourceInterfaces

open NearCubicWires

/-! ## MTT61 / CTW26 finite threshold normalization -/

def ThresholdNormalizationContract : Prop :=
  ∀ (m : ℕ), 0 < m → ∀ gate : RealThresholdGate m,
    ∃ normalized : NormalizedThresholdGate m,
      (∀ input, normalized.eval input = gate.eval input) ∧
      normalized.parametersBoundedBy (m ^ m)

/-! ## Disjoint exact decomposition — assumed object, locally proved bounds

**What is imported and what is not.**  The manuscript is explicit that the
construction here is *not* taken from the literature: Appendix A.12's
erratum-safe threshold-conversion lemma (`paper.tex:2576-2696`) replays it in
full, "because the printed proof of [CW19] Lemma 48" contains three identified
errors, and the replay "imports no one of those three literal claims"
(`paper.tex:2698-2705`).  `paper.tex:2306-2310` and `:390-391` say the same:
only the *qualitative* conversion is imported, with "all of its quantitative
bounds replayed locally".

Accordingly the published row assumes only the *existence* of a decomposition
algorithm: the stored field
`ExecutableInterfaces.ExecutableDisjointExactDecompositionContract` is now
literally `Nonempty ExecutableExactDecompositionAlgorithm`, and
`ExecutableInterfaces.executableDisjointExactDecomposition_iff_legacy`
(`TrustExactDecompositionChildCount`) proves that nothing was lost: the retired
two-clause form `LegacyDisjointExactDecompositionContract` is equivalent to it,
because the child-count clause follows from the fixed `NPOracleProgram`
interpreter ABI — the child list is decoded from the runner's single output
word, whose binary width is already charged to `runner.budget`.

Not yet formalized, and therefore still owed locally: A.12's own sharper count
`max{1, n·L̄}` with its coefficient and target envelopes.  Nothing in the
development consumes them; the interface only needs the looser
interpreter-derived bound. -/

/-! ## Williams exact Boolean rectangular multiplication -/


/-- The ordinary numeric floor of an `degree`-th root.  Mathlib's
`Nat.floorRoot` is instead the right adjoint of powers in the divisibility
order, so it is not the quantity used by rectangular multiplication or STV. -/
def integerFloorRoot (degree value : ℕ) : ℕ :=
  if degree = 0 then 0
  else Nat.findGreatest (fun candidate => candidate ^ degree ≤ value) value

theorem integerFloorRoot_pow_le
    {degree value : ℕ} (hdegree : 0 < degree) :
    integerFloorRoot degree value ^ degree ≤ value := by
  unfold integerFloorRoot
  rw [if_neg hdegree.ne']
  exact Nat.findGreatest_spec
    (P := fun candidate => candidate ^ degree ≤ value)
    (Nat.zero_le value) (by
      simp [hdegree.ne'])

theorem le_integerFloorRoot
    {degree value candidate : ℕ} (hdegree : 0 < degree)
    (hpower : candidate ^ degree ≤ value) :
    candidate ≤ integerFloorRoot degree value := by
  unfold integerFloorRoot
  rw [if_neg hdegree.ne']
  apply Nat.le_findGreatest
  · exact (Nat.le_pow hdegree).trans hpower
  · exact hpower

theorem le_integerFloorRoot_iff
    {degree value candidate : ℕ} (hdegree : 0 < degree) :
    candidate ≤ integerFloorRoot degree value ↔
      candidate ^ degree ≤ value := by
  constructor
  · intro hcandidate
    exact
      (Nat.pow_le_pow_left hcandidate degree).trans
        (integerFloorRoot_pow_le hdegree)
  · exact le_integerFloorRoot hdegree

theorem integerFloorRoot_lt_succ_pow
    {degree value : ℕ} (hdegree : 0 < degree) :
    value < (integerFloorRoot degree value + 1) ^ degree := by
  by_contra hnot
  have hnext :
      integerFloorRoot degree value + 1 ≤
        integerFloorRoot degree value :=
    le_integerFloorRoot hdegree (Nat.le_of_not_gt hnot)
  omega

theorem pow_le_integerFloorRoot_of_mul_le
    {degree base exponent totalExponent value : ℕ}
    (hdegree : 0 < degree) (hbase : 0 < base)
    (hexponent : exponent * degree ≤ totalExponent)
    (hbound : base ^ totalExponent ≤ value) :
    base ^ exponent ≤ integerFloorRoot degree value := by
  apply le_integerFloorRoot hdegree
  rw [← pow_mul]
  exact
    (Nat.pow_le_pow_right hbase hexponent).trans hbound

/-- The ordinary numeric ceiling of an `degree`-th root. -/
def integerCeilRoot (degree value : ℕ) : ℕ :=
  if degree = 0 then 0
  else
    let floor := integerFloorRoot degree value
    if floor ^ degree = value then floor else floor + 1

theorem le_integerCeilRoot_pow
    {degree value : ℕ} (hdegree : 0 < degree) :
    value ≤ integerCeilRoot degree value ^ degree := by
  unfold integerCeilRoot
  rw [if_neg hdegree.ne']
  change value ≤
    (if integerFloorRoot degree value ^ degree = value then
      integerFloorRoot degree value
    else
      integerFloorRoot degree value + 1) ^ degree
  split
  · rename_i hexact
    exact hexact.symm.le
  · exact (integerFloorRoot_lt_succ_pow hdegree).le

/-- Any integral power already below `value` is also below its ceiling root.
This one-way form is the useful capacity rule; the converse is false when the
root rounds upward. -/
theorem le_integerCeilRoot
    {degree value candidate : ℕ} (hdegree : 0 < degree)
    (hpower : candidate ^ degree ≤ value) :
    candidate ≤ integerCeilRoot degree value := by
  apply (le_integerFloorRoot hdegree hpower).trans
  unfold integerCeilRoot
  rw [if_neg hdegree.ne']
  dsimp only
  split <;> omega

theorem pow_le_integerCeilRoot_of_mul_le
    {degree base exponent totalExponent value : ℕ}
    (hdegree : 0 < degree) (hbase : 0 < base)
    (hexponent : exponent * degree ≤ totalExponent)
    (hbound : base ^ totalExponent ≤ value) :
    base ^ exponent ≤ integerCeilRoot degree value := by
  apply le_integerCeilRoot hdegree
  rw [← pow_mul]
  exact
    (Nat.pow_le_pow_right hbase hexponent).trans hbound

theorem integerCeilRoot_le
    {degree value candidate : ℕ} (hdegree : 0 < degree)
    (hpower : value ≤ candidate ^ degree) :
    integerCeilRoot degree value ≤ candidate := by
  unfold integerCeilRoot
  rw [if_neg hdegree.ne']
  change
    (if integerFloorRoot degree value ^ degree = value then
      integerFloorRoot degree value
    else
      integerFloorRoot degree value + 1) ≤ candidate
  split
  · exact (Nat.pow_le_pow_iff_left hdegree.ne').mp <|
      (integerFloorRoot_pow_le hdegree).trans hpower
  · rename_i hnotExact
    have hfloorPower :
        integerFloorRoot degree value ^ degree < candidate ^ degree :=
      (lt_of_le_of_ne (integerFloorRoot_pow_le hdegree)
        hnotExact).trans_le hpower
    have hfloor :
        integerFloorRoot degree value < candidate :=
      (Nat.pow_lt_pow_iff_left hdegree.ne').mp hfloorPower
    omega

theorem integerCeilRoot_le_iff
    {degree value candidate : ℕ} (hdegree : 0 < degree) :
    integerCeilRoot degree value ≤ candidate ↔
      value ≤ candidate ^ degree := by
  constructor
  · intro hceil
    exact (le_integerCeilRoot_pow hdegree).trans <|
      Nat.pow_le_pow_left hceil degree
  · exact integerCeilRoot_le hdegree

/-- The literal manuscript dimension `⌈U^0.1⌉`. -/
def rectangularInnerDimension (U : ℕ) : ℕ := integerCeilRoot 10 U

def integerMatrixProduct {rows inner columns : ℕ}
    (left : BitMatrix rows inner) (right : BitMatrix inner columns) :
    NatMatrix rows columns :=
  fun i j => ∑ k, if left i k && right k j then 1 else 0

/-! ## GG81 / HLW06 Margulis eight-neighbor spectrum -/

abbrev MargulisVertex (m : ℕ) [NeZero m] := ZMod m × ZMod m

def margulisNeighbor {m : ℕ} [NeZero m] (label : Fin 8)
    (vertex : MargulisVertex m) : MargulisVertex m :=
  let x := vertex.1
  let y := vertex.2
  match label.val with
  | 0 => (x + 2 * y, y)
  | 1 => (x + 2 * y + 1, y)
  | 2 => (x - 2 * y, y)
  | 3 => (x - 2 * y - 1, y)
  | 4 => (x, y + 2 * x)
  | 5 => (x, y + 2 * x + 1)
  | 6 => (x, y - 2 * x)
  | _ => (x, y - 2 * x - 1)

noncomputable def margulisAdjacency {m : ℕ} [NeZero m]
    (vector : MargulisVertex m → ℝ) (vertex : MargulisVertex m) : ℝ :=
  ∑ label : Fin 8, vector (margulisNeighbor label vertex)

def IsNontrivialMargulisEigenvalue {m : ℕ} [NeZero m]
    (eigenvalue : ℝ) : Prop :=
  ∃ vector : MargulisVertex m → ℝ,
    (∃ vertex, vector vertex ≠ 0) ∧
    (∑ vertex, vector vertex) = 0 ∧
    ∀ vertex, margulisAdjacency vector vertex = eigenvalue * vector vertex

def ExpanderSpectrumContract : Prop :=
  ∀ (m : ℕ) [NeZero m], ∀ eigenvalue : ℝ,
    IsNontrivialMargulisEigenvalue (m := m) eigenvalue →
      |eigenvalue| ≤ 5 * Real.sqrt 2 ∧ 5 * Real.sqrt 2 < 8

/-! ## RS62 Chebyshev theta estimate -/

noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log p

def PrimeThetaBoundContract : Prop :=
  ∀ x : ℝ, 563 ≤ x →
    x * (1 - 1 / (2 * Real.log x)) < chebyshevTheta x ∧
    x / 3 ≤ chebyshevTheta x

/-! ## BV/CW/CLW projection PCP and pointwise PCPP -/

structure TimedDecisionMachine where
  accepts : (n : ℕ) → BitInput n → Bool
  steps : (n : ℕ) → BitInput n → ℕ







def binaryAddress {width : ℕ} (bits : BitInput width) : Fin (2 ^ width) :=
  ⟨(∑ i, if bits i then 2 ^ i.val else 0) % (2 ^ width),
    Nat.mod_lt _ (pow_pos (by omega) _)⟩

@[simp] theorem binaryAddress_testBit {width code : ℕ}
    (hcode : code < 2 ^ width) :
    binaryAddress (fun bit : Fin width => code.testBit bit.val) =
      ⟨code, hcode⟩ := by
  apply Fin.ext
  change
    encodeBitInput (fun bit : Fin width => code.testBit bit.val) %
        2 ^ width =
      code
  rw [encodeBitInput_testBit hcode, Nat.mod_eq_of_lt hcode]

structure ProjectionPCP (machine : TimedDecisionMachine) (timeBound : ℕ → ℕ) where
  nativeWidth : ℕ → ℕ
  queryCount : ℕ → ℕ
  queryAddressBits : {n : ℕ} →
    BitInput n → Fin (queryCount n) → Fin (nativeWidth n) →
      ProjectedRandomBit (nativeWidth n)
  decision : {n : ℕ} →
    BitInput n → BitInput (nativeWidth n) → ThreeCNF (queryCount n)
  constructionSteps : ℕ → ℕ

def ProjectionPCP.queryAddress {machine : TimedDecisionMachine}
    {timeBound : ℕ → ℕ} (pcp : ProjectionPCP machine timeBound) {n : ℕ}
    (input : BitInput n) (randomness : BitInput (pcp.nativeWidth n))
    (query : Fin (pcp.queryCount n)) : Fin (2 ^ pcp.nativeWidth n) :=
  binaryAddress fun bit =>
    (pcp.queryAddressBits input query bit).eval randomness

def ProjectionPCP.accepts {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (proof : BitInput (2 ^ pcp.nativeWidth n))
    (randomness : BitInput (pcp.nativeWidth n)) :
    Bool :=
  (pcp.decision input randomness).eval
    (fun query => proof (pcp.queryAddress input randomness query))

noncomputable def ProjectionPCP.acceptanceFraction
    {machine : TimedDecisionMachine} {timeBound : ℕ → ℕ}
    (pcp : ProjectionPCP machine timeBound) {n : ℕ} (input : BitInput n)
    (proof : BitInput (2 ^ pcp.nativeWidth n)) : ℝ :=
  ((Finset.univ.filter fun randomness => pcp.accepts input proof randomness).card : ℝ) /
    (Fintype.card (BitInput (pcp.nativeWidth n)) : ℝ)



structure PointwisePCPP {n : ℕ} (circuit : BooleanCircuit n) where
  systematicBits : ℕ
  auxiliaryBits : ℕ
  clauseBits : ℕ
  systematicSupport : Fin systematicBits → Finset (Fin n)
  systematicSupportBound :
    ∀ i, (systematicSupport i).card ≤ n / 2
  clauses : Fin (2 ^ clauseBits) →
    TwoLiteralClause (systematicBits + auxiliaryBits)
  honestAuxiliary : BitInput n → BitInput auxiliaryBits
  constructionSteps : ℕ
  honestSteps : BitInput n → ℕ


noncomputable def PointwisePCPP.assignment {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (input : BitInput n)
    (auxiliary : BitInput pcpp.auxiliaryBits) :
    BitInput (pcpp.systematicBits + pcpp.auxiliaryBits) :=
  Fin.addCases
    (fun i => parityOn (pcpp.systematicSupport i) input)
    auxiliary

noncomputable def PointwisePCPP.satisfiedFraction
    {n : ℕ} {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (input : BitInput n) (auxiliary : BitInput pcpp.auxiliaryBits) : ℝ :=
  ((Finset.univ.filter fun i =>
    (pcpp.clauses i).eval (pcpp.assignment input auxiliary)).card : ℝ) /
    (2 ^ pcpp.clauseBits : ℝ)

/-! ## CLW fixed-machine refuter and XOR interface -/


/-- A deliberately conservative subfamily of the CLW clock range.  Polynomial
clocks are enough for the transfer and automatically satisfy the source
theorem's single-exponential upper restriction. -/
def PolynomiallyBounded (bound : ℕ → ℕ) : Prop :=
  ∃ coefficient degree : ℕ, 0 < coefficient ∧
    ∀ n, bound n ≤ coefficient * (n + 1) ^ degree

structure WeakNondeterministicMachine where
  witnessBits : ℕ → ℕ
  run : (n : ℕ) → BitInput n → BitInput (witnessBits n) → Bool
  steps : (n : ℕ) → BitInput n → BitInput (witnessBits n) → ℕ

def WeakNondeterministicMachine.accepts (machine : WeakNondeterministicMachine)
    {n : ℕ} (input : BitInput n) : Prop :=
  ∃ witness, machine.run n input witness

def RunsInLittleO (machine : WeakNondeterministicMachine)
    (bound : ℕ → ℕ) : Prop :=
  ∀ multiplier : ℕ, 0 < multiplier →
    ∃ onset, ∀ n, onset ≤ n → ∀ input witness,
      multiplier * machine.steps n input witness ≤ bound n

def blockInput {n k : ℕ} (input : BitInput (k * n)) (block : Fin k) :
    BitInput n :=
  fun index => input ⟨block.val * n + index.val, by
    have h₁ : block.val * n + index.val < block.val * n + n :=
      Nat.add_lt_add_left index.isLt _
    have h₂ : block.val * n + n ≤ k * n := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right n (Nat.succ_le_iff.mpr block.isLt)
    exact lt_of_lt_of_le h₁ h₂⟩

noncomputable def xorPower {n : ℕ} (function : BoolFunction n) (k : ℕ) :
    BoolFunction (k * n) :=
  fun input =>
    (Finset.univ : Finset (Fin k)).toList.foldl
      (fun parity block => xor parity (function (blockInput input block)))
      false

abbrev SizedFunctionFamily :=
  (n : ℕ) → BoolFunction n → ℕ → Prop

/-- **The other half of the same licence.**  `paper.tex:4364-4366` allows the
atoms to be restrictions *or negated restrictions* of `C`, and asserts that
**both** operations preserve the two target classes and their wires;
`paper.tex:617` gives the negation half explicitly:

> Output negation changes only the symmetric lookup, or replaces a top
> inequality `L ≥ θ` by `-L ≥ -θ+1`, so it also preserves the class and wire
> count.

Note the size argument is the *same* on both sides: negation is charged no
wires, which is exactly what the manuscript claims. -/
def NegationClosedFamily (family : SizedFunctionFamily) : Prop :=
  ∀ {n size : ℕ} (candidate : BoolFunction n),
    family n candidate size →
      family n (fun input => !candidate input) size

/-- The XOR source produces finite rational linear combinations.  Keeping the
coefficients rational here is load-bearing: the componentwise weak machine can
decode exactly the same objects, while `value` below performs the sole coercion
to the real semantics used by distance and agreement. -/
structure UnitIntervalCircuitSum (family : SizedFunctionFamily)
    (n size : ℕ) where
  terms : List (ℚ × BoolFunction n)
  legal : ∀ term ∈ terms, family n term.2 size
  inUnitInterval : ∀ input,
    0 ≤ terms.foldl
      (fun total term => total + (term.1 : ℝ) * bitAsReal (term.2 input)) 0 ∧
    terms.foldl
      (fun total term => total + (term.1 : ℝ) * bitAsReal (term.2 input)) 0 ≤ 1

noncomputable def UnitIntervalCircuitSum.value
    {family : SizedFunctionFamily} {n size : ℕ}
    (sum : UnitIntervalCircuitSum family n size) (input : BitInput n) : ℝ :=
  sum.terms.foldl
    (fun total term => total + (term.1 : ℝ) * bitAsReal (term.2 input)) 0

noncomputable def UnitIntervalCircuitSum.coefficientMass
    {family : SizedFunctionFamily} {n size : ℕ}
    (sum : UnitIntervalCircuitSum family n size) : ℝ :=
  sum.terms.foldl (fun total term => total + |(term.1 : ℝ)|) 0

noncomputable def l1DistanceFromBoolean {n : ℕ} (function : BoolFunction n)
    (approximation : BitInput n → ℝ) : ℝ :=
  (∑ input, |approximation input - bitAsReal (function input)|) /
    (Fintype.card (BitInput n) : ℝ)

noncomputable def xorEpsilon (delta : ℝ) (k : ℕ) : ℝ :=
  (1 - delta) ^ (k - 1) * (1 / 2 - delta)

/-! ## CLW/STV worst-case amplifier -/

def WorstCaseHardAt (function : BoolFunction n) (sizeBound : ℕ) : Prop :=
  ∀ circuit : BooleanCircuit n, circuit.size ≤ sizeBound →
    ∃ input, circuit.eval input ≠ function input

structure AmplifiedTruthTable (n : ℕ) where
  outputArity : ℕ
  function : BoolFunction outputArity
  constructionSteps : ℕ

end NearCubicWires.SourceInterfaces
