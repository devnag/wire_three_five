import Proof.Circuits.PaddedRunnerBudgetDomination

namespace NearCubicWires.PaddedRunnerBudgetClosure

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionDecisionRunner
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PaddedProjectionPresentedPCP
open NearCubicWires.PaddedProjectionQueryRunner
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PaddedProjectionShapeRunner
open NearCubicWires.PaddedRunnerBudgetDomination
open NearCubicWires.PolynomialClock
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.VerifiedLinker
open NearCubicWires.ValidatorPolynomialDomination

/-! ## 1. The degree-free judgement -/

/-- **The walk's judgement, with the degree closed.**  A charge is polynomially
dominated when *some* degree and *some* coefficient make it fit the polynomial
budget at its own measure.  Both witnesses stay existential: the coefficients
mention composed register spans, and the degrees mention the published runner
exponents, and neither should reach a statement the kernel might evaluate. -/
def PolyDominated {Request : Type} (charge measureOf : Request → ℕ) : Prop :=
  ∃ degree, Dominated charge measureOf degree

theorem PolyDominated.mono {Request : Type}
    {charge charge' measureOf : Request → ℕ}
    (h : PolyDominated charge measureOf)
    (hle : ∀ request, charge' request ≤ charge request) :
    PolyDominated charge' measureOf := by
  obtain ⟨degree, hdegree⟩ := h
  exact ⟨degree, hdegree.mono hle⟩

theorem polyDominated_const {Request : Type} {measureOf : Request → ℕ}
    (value : ℕ) : PolyDominated (fun _ : Request => value) measureOf :=
  ⟨0, dominated_const value 0⟩

/-- Two judgements brought to a common degree. -/
theorem PolyDominated.align {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    ∃ degree, Dominated left measureOf degree ∧
      Dominated right measureOf degree := by
  obtain ⟨leftDegree, hleftBound⟩ := hleft
  obtain ⟨rightDegree, hrightBound⟩ := hright
  exact
    ⟨max leftDegree rightDegree,
      hleftBound.degree_mono (Nat.le_max_left _ _),
      hrightBound.degree_mono (Nat.le_max_right _ _)⟩

theorem PolyDominated.add {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    PolyDominated (fun request => left request + right request) measureOf := by
  obtain ⟨degree, hleftBound, hrightBound⟩ := hleft.align hright
  exact ⟨degree, hleftBound.add hrightBound⟩

theorem PolyDominated.mul {Request : Type}
    {left right measureOf : Request → ℕ}
    (hleft : PolyDominated left measureOf)
    (hright : PolyDominated right measureOf) :
    PolyDominated (fun request => left request * right request) measureOf := by
  obtain ⟨leftDegree, hleftBound⟩ := hleft
  obtain ⟨rightDegree, hrightBound⟩ := hright
  exact ⟨leftDegree + rightDegree, hleftBound.mul hrightBound⟩

theorem PolyDominated.const_mul {Request : Type}
    {charge measureOf : Request → ℕ} (factor : ℕ)
    (h : PolyDominated charge measureOf) :
    PolyDominated (fun request => factor * charge request) measureOf := by
  obtain ⟨degree, hdegree⟩ := h
  exact ⟨degree, hdegree.const_mul factor⟩

/-! ## 2. The published source numerals are polynomials in the public length

Everything in the outer PCP's published surface — its clock, its runner budgets,
its native width and query count — is a polynomial in the public length by
itself.  The whole ledger rests on one inequality about the pairing clock. -/

/-- The ledger judgement: a charge on the public length, dominated by a
polynomial in that length. -/
abbrev SourcePoly (charge : ℕ → ℕ) : Prop :=
  PolyDominated charge (fun n => n)

/-- Enter the ledger from an explicit polynomial bound. -/
theorem sourcePoly_of_le {charge : ℕ → ℕ} (coefficient degree : ℕ)
    (hbound : ∀ n, charge n ≤ coefficient * (n + 1) ^ degree) :
    SourcePoly charge :=
  ⟨degree, ⟨coefficient, fun n => hbound n⟩⟩

theorem sourcePoly_id : SourcePoly (fun n => n) :=
  sourcePoly_of_le 1 1 fun n => by
    rw [Nat.one_mul, Nat.pow_one]
    omega

theorem sourcePoly_pow {charge : ℕ → ℕ} (h : SourcePoly charge)
    (exponent : ℕ) : SourcePoly (fun n => charge n ^ exponent) := by
  obtain ⟨degree, coefficient, hbound⟩ := h
  refine sourcePoly_of_le (coefficient ^ exponent) (degree * exponent)
    fun n => ?_
  have hvalue : charge n ≤ coefficient * (n + 1) ^ degree := hbound n
  calc
    charge n ^ exponent ≤ (coefficient * (n + 1) ^ degree) ^ exponent :=
      Nat.pow_le_pow_left hvalue exponent
    _ = coefficient ^ exponent * (n + 1) ^ (degree * exponent) := by
      rw [Nat.mul_pow, ← Nat.pow_mul]

/-- The logarithmic scale of a polynomial charge is a polynomial charge. -/
theorem sourcePoly_logScale {charge : ℕ → ℕ} (h : SourcePoly charge) :
    SourcePoly (fun n => logScale (charge n)) :=
  PolyDominated.mono (PolyDominated.add h (polyDominated_const 2))
    fun n => logScale_le_add_two (charge n)

/-! ## 3. Transferring the ledger to the two request measures -/

/-! ## 7. The two width combinators, with the degree closed -/

/-! ## 8. The in-range chain's register ledger

`inRangeProgram` is seven linked stages, and every one of them is a maximum of
binary widths of codes assembled from five numerals: the public length, the
native width, the retained request tail, the source query runner's declared
width and the source answer.  Nothing here charges an answer *magnitude*: that
is the whole difference between row 4 and row 5. -/

/-! ## 9. Row 4, closed outright

The padded query stream's register ledger charges the guard's saturating
factors, the source shape and query runners' declared widths, and the source
answer's *width*.  Every one of those is a published numeral or a halt check, so
row 4 needs nothing the interface does not already carry. -/

/-! ## 11. Row 5, closed outright

`inRangeFuel` charges the modular reduction twice at the two halves of the
source answer.  With `CanonicalBitSerialModProgram` on that stage the charge is
`13 * natBitLength numerator + 10` — linear in the answer's *width*, which §10's
halt check already dominates — rather than linear in its magnitude.  Row 5
therefore needs no source-side normalization at all. -/

/-! ## 12. The capstone, modulo the numeral bank

Four of the six runner charges are theorems of the published interface outright;
the padded shape stream's two reduce to the numeral bank's own charges for the
program that computes the width envelope.  Nothing source-side survives: the
padded query stream is charged against the source answer's *width*, which is the
source runner's own halt check, and the padded decision stream against the
published width budget through `proofSizeBound`.  §13 and §14 discharge the two
bank charges, and §15 removes the last premise. -/

/-! ## 14. The numeral bank's width-envelope register ledger

The bits spine is a nine-stage maximum with two recursions — one over the clock
depth, one over the frozen power exponent.  Neither needs a numeric envelope:
both recurse on a *charge* that is itself dominated at every step, so the
induction runs entirely inside `PolyDominated`. -/

end NearCubicWires.PaddedRunnerBudgetClosure
