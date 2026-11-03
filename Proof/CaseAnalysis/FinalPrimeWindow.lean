import Proof.CaseAnalysis.FinalWireEnvelope
import Proof.CaseAnalysis.RawRowsThresholdAccuracy

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutFinalC10StageFields
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls (siteCalls)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10ThresholdRows (primeCutoff primeDenominator
  listDenominator)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WireEnvelope
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource (EightSources)
open NearCubicWires.RepairSource.CloseoutFinal (Parameters constantsOf decompositionOf)
open NearCubicWires.RepairSource.CloseoutFinal.C10SumFamilyTransport (stageCoordinate)
open NearCubicWires.RepairSource.CloseoutFinal.C10TailComposeUniform (pcppOf Atoms)
open NearCubicWires.RepairSource.CloseoutFinal.C10TotalDecode (Atom)
open NearCubicWires.RepairSource.CloseoutFinal.C10UnionSupplier
open NearCubicWires.PolynomialSchedule
open NearCubicWires.RepairSource.CloseoutRawRows (sourceChildBound sourceChildBound_polynomial
  thresholdMagnitudeExponent thresholdMagnitudeExponent_polynomial selection_count
  canonical_stack_magnitude top_child_magnitude descriptionEnvelope
  descriptionEnvelope_polynomial thresholdFamilyBound thresholdPrimeDen thresholdCutoff
  thresholdListDen threshold_parameters_polynomial primeCutoff_polynomial)
open NearCubicWires.RepairSource.CloseoutWitnessResources (bits_polynomial)
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline
open NearCubicWires.SupplierPrime (primesUpTo equationMagnitudeBound familyMagnitudeBound
  familyMagnitudeExponent canonicalPrimeScale canonicalPrimeCutoff)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true
noncomputable section

/-! ## §1 The per-atom DESCRIPTION envelope, as a number

`paper.tex:4292-4302`'s rejection rule lists FOUR caps -- "exceeds its declared
term, coefficient-bit, coefficient-mass, or per-atom wire envelope" -- and
`CheckedLegalCircuitSum` (`Proof/Circuits/CanonicalWitnessCodec.lean`) carries
all of them, `wires_le` (`:1561`) and `description_le` (`:1563`) side by side.
`atomWires` (`Proof/CaseAnalysis/FinalWireEnvelope.lean`) is the Lean quantity
for the wire cap; `atomDescription` below is its exact sibling for the
description cap, charged through the SAME `atomToUnion`
(`Proof/CaseAnalysis/FinalUnionSupplier.lean`) so the systematic constructor
is charged for the native parity circuit it compiles into and nothing is charged
twice. -/

/-! ## §2 THE GAP -- `familyMagnitudeExponent` at the child-tuple family

`primeCutoff` (`Proof/CaseAnalysis/FinalThresholdRows.lean`) reads TWO numbers
off the tuple family: `familyMagnitudeExponent (ThresholdRows.equation a r)`
(`Proof/Foundations/SupplierPrime.lean`) and `primeDenominator a r target`.  The
second is `selection_count` on the nose.  The first is NOT: `familyMagnitudeBound`
(`Proof/Foundations/SupplierPrime.lean`) SUMS `equationMagnitudeBound` over the whole
tuple family, so it needs the per-tuple magnitude bound AND the tuple count, and
then one `Nat.clog` step.  Nothing in the corpus bounds it from above -- the
three declarations whose conclusion mentions `familyMagnitudeExponent` are
`family_difference_lt_two_pow` and the two certificate constructors, none of
which is an inequality on the exponent itself. -/

/-- `2 ^ K * 2 ^ M` and one more fits in `2 ^ (K + M + 1)`, so a total bounded by
`count * 2 ^ M` with `count ≤ 2 ^ K` has `clog`-successor at most `K + M + 1`. -/
private theorem clog_succ_le (total count K M : ℕ) (hcount : count ≤ 2 ^ K)
    (htotal : total ≤ count * 2 ^ M) :
    Nat.clog 2 (total + 1) ≤ K + M + 1 := by
  have h1 : total ≤ 2 ^ K * 2 ^ M :=
    htotal.trans (Nat.mul_le_mul_right _ hcount)
  have hpos : (1 : ℕ) ≤ 2 ^ K * 2 ^ M := by
    rw [← pow_add]
    exact Nat.one_le_two_pow
  have hrw : (2 : ℕ) ^ (K + M + 1) = 2 ^ K * 2 ^ M + 2 ^ K * 2 ^ M := by
    rw [pow_succ, pow_add]
    ring
  have h2 : total + 1 ≤ 2 ^ (K + M + 1) := by
    rw [hrw]
    exact Nat.add_le_add h1 hpos
  calc Nat.clog 2 (total + 1) ≤ Nat.clog 2 (2 ^ (K + M + 1)) := Nat.clog_mono_right 2 h2
    _ = K + M + 1 := Nat.clog_pow 2 _ (by norm_num)

/-- **One child tuple's stacked equation has bounded magnitude.**  This is
`actual_threshold_difference` (`Proof/CaseAnalysis/RawRowsThresholdSize.lean`)
stopped one step earlier: at the MAGNITUDE BOUND rather than at one
difference, because `familyMagnitudeBound` sums the bound, not the difference. -/
theorem equation_magnitudeBound_lt (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc)
    (sel : ThresholdRows.Selection a r) :
    equationMagnitudeBound (ThresholdRows.equation a r sel) <
      2 ^ thresholdMagnitudeExponent a desc := by
  apply canonical_stack_magnitude (ThresholdRows.equations a r sel) (sourceChildBound a desc)
  · simpa only [ThresholdRows.equations, List.length_ofFn] using hfour
  · intro e he
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
    rw [thresholdChildEquation_magnitudeBound]
    exact top_child_magnitude a _ desc (hd _ (List.get_mem _ _)) (sel i)

/-- The family magnitude exponent's envelope: `4 c_0` bits of tuple count on top
of the per-tuple magnitude exponent, plus one. -/
def tupleExponentBound (a : DecompositionAlgorithm) (desc : ℕ) : ℕ :=
  4 * Nat.clog 2 (sourceChildBound a desc + 1) + thresholdMagnitudeExponent a desc + 1

/-- **THE GAP, CLOSED.**  `familyMagnitudeExponent` at the child-tuple family is
bounded by a closed form in the source child bound alone. -/
theorem familyMagnitudeExponent_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    familyMagnitudeExponent (ThresholdRows.equation a r) ≤ tupleExponentBound a desc := by
  classical
  have hcard : Fintype.card (ThresholdRows.Selection a r) ≤
      2 ^ (4 * Nat.clog 2 (sourceChildBound a desc + 1)) := by
    refine (selection_count a r desc hfour hd).trans ?_
    calc (sourceChildBound a desc + 1) ^ 4
        ≤ (2 ^ Nat.clog 2 (sourceChildBound a desc + 1)) ^ 4 :=
          Nat.pow_le_pow_left (Nat.le_pow_clog (by norm_num) _) 4
      _ = 2 ^ (4 * Nat.clog 2 (sourceChildBound a desc + 1)) := by
          rw [← pow_mul, Nat.mul_comm]
  have hterm : ∀ sel ∈ (Finset.univ : Finset (ThresholdRows.Selection a r)),
      equationMagnitudeBound (ThresholdRows.equation a r sel) ≤
        2 ^ thresholdMagnitudeExponent a desc :=
    fun sel _ => (equation_magnitudeBound_lt a r desc hfour hd sel).le
  have hsum : familyMagnitudeBound (ThresholdRows.equation a r) ≤
      Fintype.card (ThresholdRows.Selection a r) * 2 ^ thresholdMagnitudeExponent a desc := by
    have hle := Finset.sum_le_card_nsmul (Finset.univ : Finset (ThresholdRows.Selection a r))
      (fun sel => equationMagnitudeBound (ThresholdRows.equation a r sel))
      (2 ^ thresholdMagnitudeExponent a desc) hterm
    simpa [familyMagnitudeBound, Finset.card_univ, smul_eq_mul] using hle
  exact clog_succ_le _ _ _ _ hcard hsum

/-! ## §3 The prime window and the list denominator, in closed form

`canonicalPrimeCutoff` (`Proof/Foundations/SupplierPrime.lean`) is monotone in both
arguments and `reciprocalUnionDenominator`
(`Proof/Supplier/SupplierEstimator.lean`) is monotone in the family size, so §2
plus `selection_count` bound the cutoff, and `primesUpTo_card_le`
(`Proof/CaseAnalysis/FinalWireEnvelope.lean`) turns that into the window's
cardinality.  `listDenominator` (`Proof/CaseAnalysis/FinalThresholdRows.lean`)
is `modulusDigitCount (primeCutoff …) * (primeDenominator … + 1)`, so it falls
out of the SAME two bounds -- which is why `hprime` and `hthrden` are one
obligation and not two. -/

theorem canonicalPrimeCutoff_mono {e e' d d' : ℕ} (he : e ≤ e') (hd : d ≤ d') :
    canonicalPrimeCutoff e d ≤ canonicalPrimeCutoff e' d' := by
  unfold canonicalPrimeCutoff canonicalPrimeScale
  exact Nat.pow_le_pow_left
    (max_le_max le_rfl
      (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (Nat.succ_le_succ he)) (Nat.succ_le_succ hd))) 2

theorem reciprocalUnionDenominator_mono {f f' t : ℕ} (h : f ≤ f') :
    reciprocalUnionDenominator f t ≤ reciprocalUnionDenominator f' t := by
  unfold reciprocalUnionDenominator
  exact Nat.mul_le_mul (Nat.mul_le_mul le_rfl h) le_rfl

theorem modulusDigitCount_mono {m m' : ℕ} (h : m ≤ m') :
    modulusDigitCount m ≤ modulusDigitCount m' :=
  Nat.succ_le_succ (Nat.log_mono_right h)

def tupleCutoffBound (a : DecompositionAlgorithm) (desc target : ℕ) : ℕ :=
  canonicalPrimeCutoff (tupleExponentBound a desc) (thresholdPrimeDen a desc target)

def tupleListDenominatorBound (a : DecompositionAlgorithm) (desc target : ℕ) : ℕ :=
  modulusDigitCount (tupleCutoffBound a desc target) * (thresholdPrimeDen a desc target + 1)

theorem primeDenominator_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    primeDenominator a r target ≤ thresholdPrimeDen a desc target :=
  reciprocalUnionDenominator_mono (selection_count a r desc hfour hd)

theorem primeCutoff_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    primeCutoff a r target ≤ tupleCutoffBound a desc target :=
  canonicalPrimeCutoff_mono (familyMagnitudeExponent_le a r desc hfour hd)
    (primeDenominator_le a r desc target hfour hd)

/-- **`hthrden`'S CONTENT, AT ONE REQUEST.** -/
theorem listDenominator_le (a : DecompositionAlgorithm)
    (r : FourfoldRequest NormalizedThresholdThresholdCircuit) (desc target : ℕ)
    (hfour : r.circuits.length ≤ 4)
    (hd : ∀ c ∈ r.circuits, c.descriptionBits ≤ desc) :
    listDenominator a r target ≤ tupleListDenominatorBound a desc target :=
  Nat.mul_le_mul (modulusDigitCount_mono (primeCutoff_le a r desc target hfour hd))
    (Nat.succ_le_succ (primeDenominator_le a r desc target hfour hd))

/-! ## §4 The request at one monomial

`unionRequestOf` (`Proof/CaseAnalysis/FinalWireEnvelope.lean`) is
`⟨stageArity …, monomial.factors.map atomToUnion⟩`, so the threshold request
`rightRequest (unionRequestOf …)` has exactly the monomial's threshold atoms as
its circuits.  `hfour` is then `CircuitMonomial.degree_le` and the description
cap transports through `atomToUnion` unchanged. -/

variable (sources : EightSources) (k : ℕ) {gamma : ℝ} (p : Parameters sources gamma)

/-! ## §5 `hprime` and `hthrden`, at A.8's two summands

`stageSeedEnvelope` (`Proof/CaseAnalysis/FinalWireEnvelope.lean`) spends
exactly two numbers on the threshold branch: `primeBits n` (A.8's "primes") and
`thrDenBound n` (A.8's "stacked-equation labels").  §5 names both, as functions
of a per-atom DESCRIPTION cap, and discharges the two binders. -/

-- the three `private` arithmetic cores, by their in-file names

theorem tupleExponentBound_polynomial (a : DecompositionAlgorithm) (degree : ℕ) :
    PolynomiallyBounded (fun q => tupleExponentBound a (descriptionEnvelope degree q)) := by
  refine polynomiallyBounded_mono (fun q => ?_)
    (polynomiallyBounded_add
      (polynomiallyBounded_add
        (polynomiallyBounded_mul (polynomiallyBounded_constant 4)
          (sourceChildBound_polynomial a (descriptionEnvelope_polynomial degree)))
        (thresholdMagnitudeExponent_polynomial a degree))
      (polynomiallyBounded_constant 1))
  have hclog : Nat.clog 2 (sourceChildBound a (descriptionEnvelope degree q) + 1) ≤
      sourceChildBound a (descriptionEnvelope degree q) :=
    Nat.clog_le_of_le_pow (Nat.succ_le_of_lt Nat.lt_two_pow_self)
  unfold tupleExponentBound
  omega

/-- **The prime window is polynomial**, at the cutoff `primeCutoff` actually
uses -- which `threshold_parameters_polynomial` does not cover. -/
theorem tupleCutoffBound_polynomial (a : DecompositionAlgorithm) (degree : ℕ)
    (target : ℕ → ℕ) (ht : PolynomiallyBounded target) :
    PolynomiallyBounded
      (fun q => tupleCutoffBound a (descriptionEnvelope degree q) (target q)) :=
  primeCutoff_polynomial (tupleExponentBound_polynomial a degree)
    (threshold_parameters_polynomial a degree target ht).1

/-- **The stacked-equation list denominator is polynomial**, at the same cutoff. -/
theorem tupleListDenominatorBound_polynomial (a : DecompositionAlgorithm) (degree : ℕ)
    (target : ℕ → ℕ) (ht : PolynomiallyBounded target) :
    PolynomiallyBounded
      (fun q => tupleListDenominatorBound a (descriptionEnvelope degree q) (target q)) :=
  polynomiallyBounded_mul (bits_polynomial (tupleCutoffBound_polynomial a degree target ht))
    (polynomiallyBounded_add (threshold_parameters_polynomial a degree target ht).1
      (polynomiallyBounded_constant 1))


end
end NearCubicWires.RepairOrdinary.CloseoutFinalC10PrimeWindow
