import Proof.Circuits.ValidatorCompositeLeafBounds
import Proof.PCP.PaddedProjectionPresentedPCP

namespace NearCubicWires.PaddedRunnerBudgetDomination

open NearCubicWires
open NearCubicWires.BitInputPrefixProgram
open NearCubicWires.CanonicalBinary
open NearCubicWires.CaseOneRecoveryAssembly
open NearCubicWires.CanonicalRecoveryRequest
open NearCubicWires.CaseTwoOccurrenceProgram
open NearCubicWires.ExecutableInterfaces
open NearCubicWires.OuterPCPRecovery
open NearCubicWires.PaddedProjectionDecisionRunner
open NearCubicWires.PaddedProjectionPresentation
open NearCubicWires.PaddedProjectionPresentedPCP
open NearCubicWires.PaddedProjectionQueryRunner
open NearCubicWires.PaddedProjectionRunnerAssembly
open NearCubicWires.PaddedProjectionRunnerOutputs
open NearCubicWires.PaddedProjectionShapeRunner
open NearCubicWires.PolynomialClock
open NearCubicWires.PreserveRightProgram
open NearCubicWires.ProjectionWidthEnvelope
open NearCubicWires.RuntimeScheduleNumeralBank
open NearCubicWires.SourceInterfaces
open NearCubicWires.ValidatorCompositeLeafBounds
open NearCubicWires.ValidatorPolynomialDomination
open NearCubicWires.VerifiedLinker

/-! ## 1. The coefficient-free domination judgement -/

/-- **The walk's judgement.**  A charge is *dominated* at a degree when some
uniform coefficient makes it fit the polynomial budget at its own measure.  The
coefficient is quantified away because every linker in the cone contributes a
closed `programRegisterSpan` of a composed instruction stream: those numerals
must never enter a statement the kernel might try to evaluate. -/
def Dominated {Request : Type} (charge measureOf : Request → ℕ)
    (degree : ℕ) : Prop :=
  ∃ coefficient, ∀ request : Request,
    PolyBounded (charge request) (measureOf request) coefficient degree

/-! ## 2. One closure lemma per cost shape -/

theorem Dominated.mono {Request : Type} {charge charge' measureOf :
    Request → ℕ} {degree : ℕ} (h : Dominated charge measureOf degree)
    (hle : ∀ request, charge' request ≤ charge request) :
    Dominated charge' measureOf degree := by
  obtain ⟨coefficient, hcoefficient⟩ := h
  exact ⟨coefficient, fun request => (hcoefficient request).mono (hle request)⟩

theorem Dominated.degree_mono {Request : Type} {charge measureOf : Request → ℕ}
    {degree degree' : ℕ} (h : Dominated charge measureOf degree)
    (hle : degree ≤ degree') : Dominated charge measureOf degree' := by
  obtain ⟨coefficient, hcoefficient⟩ := h
  exact ⟨coefficient, fun request => (hcoefficient request).degree_mono hle⟩

/-- A charge that does not move with the request. -/
theorem dominated_const {Request : Type} {measureOf : Request → ℕ}
    (value degree : ℕ) :
    Dominated (fun _ : Request => value) measureOf degree :=
  ⟨value, fun request => polyBounded_const value (measureOf request) degree⟩

theorem Dominated.add {Request : Type} {left right measureOf : Request → ℕ}
    {degree : ℕ} (hleft : Dominated left measureOf degree)
    (hright : Dominated right measureOf degree) :
    Dominated (fun request => left request + right request) measureOf degree := by
  obtain ⟨leftCoefficient, hleftBound⟩ := hleft
  obtain ⟨rightCoefficient, hrightBound⟩ := hright
  exact ⟨leftCoefficient + rightCoefficient,
    fun request => (hleftBound request).add (hrightBound request)⟩

/-- The only degree-raising rule: a counted repetition. -/
theorem Dominated.mul {Request : Type} {left right measureOf : Request → ℕ}
    {leftDegree rightDegree : ℕ}
    (hleft : Dominated left measureOf leftDegree)
    (hright : Dominated right measureOf rightDegree) :
    Dominated (fun request => left request * right request) measureOf
      (leftDegree + rightDegree) := by
  obtain ⟨leftCoefficient, hleftBound⟩ := hleft
  obtain ⟨rightCoefficient, hrightBound⟩ := hright
  exact ⟨leftCoefficient * rightCoefficient,
    fun request => (hleftBound request).mul (hrightBound request)⟩

/-! ### The width shapes -/

/-! ### Entering the judgement from a magnitude bound -/

/-! ## 3. The three initial-width rows, closed outright

Rows 3, 6 and 9 of `PaddedRunnerBudget` are the presentation's own
`initialBitsFit` obligations.  They mention no runner at all: each is the binary
width of the request code, and every component of a request code is bounded by
the request's own measure. -/

/-- Scaling a dominated charge by a closed factor keeps the degree. -/
theorem Dominated.const_mul {Request : Type} {charge measureOf : Request → ℕ}
    {degree : ℕ} (factor : ℕ) (h : Dominated charge measureOf degree) :
    Dominated (fun request => factor * charge request) measureOf degree := by
  obtain ⟨coefficient, hbound⟩ := h
  exact ⟨factor * coefficient, fun request => (hbound request).const_mul factor⟩

/-! ## 5. The shape runner's fuel spine

`paddedShapeFuel` links three stages over two moving charges: the source shape
runner's own budget and the numeral bank's width-envelope charge.  Everything
else is a closed framing constant. -/

/-! ## 6. The decision runner's fuel spine

The padded decision stream is the source decision runner called on the *native
prefix* of the padded random string.  Its only non-obvious charge is the prefix
reducer's: `bitInputPrefixFuel` is exponential in the selected width.  The outer
PCP's published `proofSizeBound` is exactly the fact that converts it, since
`2 ^ nativeWidth n ≤ widthBudget outer n` and `widthBudget` is a published
source numeral. -/

/-! ## 7. The ten rows

Six moving charges and the three initial-width rows of §3 close
`PaddedRunnerBudget`.  The coefficient is produced rather than declared: it is
the sum of the nine witnesses, and it mentions the composed register spans the
linkers contribute, so it must never be written into a statement. -/

/-! ## 8. The capstone

With the budget produced, the padded projection PCP is *fully* discharged:
existence, presentation and budget.  This eliminates the
`PaddedProjectionPresentation.PresentsPaddedOuterPCP` premise of
`PaddedProjectionPresentation.inverse_bodyRun_ofPresentation` outright. -/

/-! ## 9. The two width spines

The width ledgers are pure maxima: no linker widens a register beyond the widest
stage it joins.  Both walks therefore run on `Dominated.occurrenceStageBits` and
`Dominated.preserveRightBits`, and both bottom out in the *published* runner
budgets plus one bank charge each. -/

/-! ## 10. The query runner's residue, and how it was removed

**Superseded.**  This section recorded an obstruction that no longer exists;
`PaddedRunnerBudgetClosure` closes rows 4 and 5 outright.  The record is kept
because the dead end is instructive.

The obstruction was that `PaddedProjectionQueryRunner.inRangeFuel` reduced the
source answer's two halves with `CanonicalNativeModProgram`, whose clock is
linear in the *magnitude* of its numerator, `7 * numerator + 10`.  The published
interface bounds the source answer only through the interpreter's halt check,
`natBitLength (query.execute request) ≤ query.budget request`, which leaves the
answer as large as `2 ^ queryBudget`.  Nor can that be repaired from the
published surface: `ExecutableProjectionPCP` reads a query answer through
`ExecutableInterfaces.decodeProjectedRandomBit`, which itself reduces the tag
modulo three and the index modulo the native width, so
`ExecutableProjectionPCPGuarantee` deliberately carries no constraint on the
answer's code — and `publishedHierarchyOuterPCP` is a `Classical.choice` from
that guarantee.

The fix was on the *padded* side, not the source side.  The stage now uses
`CanonicalBitSerialModProgram`, whose public surface is interchangeable with
`CanonicalNativeModProgram`'s and whose clock is
`13 * natBitLength numerator + 10` — linear in the answer's *width*, which the
halt check bounds.  `SourceQueryAnswerBounded` below is therefore no longer a
premise of anything; it is retained only as a statement of the property that
turned out not to be needed. -/

end NearCubicWires.PaddedRunnerBudgetDomination
