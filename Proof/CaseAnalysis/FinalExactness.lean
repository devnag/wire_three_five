import Proof.CaseAnalysis.RowsOriginalScheduleMeaning
import Proof.Circuits.AggregateClauseExpansion

/-!
# P3a — C.10 exactness: the three grouped phase means ARE finite AND-four
supplier expansions

Paper C.10 (paper.tex:4098-4160).  The weak machine "estimates
`mu = E_{i,u} F_i(u)` **by expanding it into AND-four supplier calls**", it
"estimates `E_{i,j,u} P_ij` and every `E_u Q_ij`", "all expressions have degree
at most four in the guessed sums", and "no parity-support enumeration occurs".

This module proves the EXACT identity behind that sentence, for all three of
`RepairCloseoutRowsOriginalSchedule`'s grouped phases at once:

```
mean ph pcpp proofValue = (phasePolynomial ph pcpp coordinate systematicAtom).exactMean evaluate
                        = sum over monomials of  coefficient * conjunctionProbability evaluate factors
```

with no error term.  `CircuitPolynomial.exactMean` IS the paper's expansion:
one `conjunctionProbability evaluate factors` per monomial is exactly one
supplier call, and `CircuitMonomial.degree_le` at degree `4` is exactly the
"AND-four" ABI.

## What the machine must range over

`sitePolynomial ph pcpp coordinate systematicAtom i` is the polynomial of ONE
site, and the site index is `i : Fin (2 ^ pcpp.clauseBits)` -- the PCPP clause
address, and nothing else.  `mean_eq_site_expect` states the whole mean as the
uniform average of the site polynomials' exact means.  `BitInput n` is never
enumerated: the `u`-average lives entirely inside `conjunctionProbability`,
which is what the supplier returns.  That is the paper's "no parity-support
enumeration occurs".

## The restriction seam

`CoordinateExpands` is the only hypothesis about the guessed proof: each
recovered PCPP coordinate is one linear polynomial in supplier circuits at
arity `n`.  It is strictly weaker than
`AggregateClauseExpansion.SliceRestricts` (which implies it through the GREEN
`occurrenceCoordinatePolynomial_value`), and it is met directly by
`CloseoutWitness.SumFamily.value`, whose per-variable sum IS a linear
polynomial in supplier circuits.  So this statement composes with BOTH the
occurrence-slice presentation and the witness-family presentation.

The systematic atoms enter as `systematicAtom` + `hsystematic`, exactly as in
the GREEN `AggregateSemanticAggregateClausePenaltyPolynomial`: a single parity
CIRCUIT per systematic coordinate, never an enumeration of its support.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateClauseExpansion
open NearCubicWires.AggregateSemanticStage
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ComponentwiseValidity
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §0 Generic polynomial arithmetic -/

/-- A list sum, as a `Finset` sum over the list's own index type.  This is the
shape `Realizes.hexpansion` is stated in. -/
theorem listSum_eq_finsetSum {α β : Type} [AddCommMonoid β]
    (values : List α) (map : α → β) :
    (values.map map).sum = ∑ i : Fin values.length, map values[i] := by
  induction values with
  | nil => simp
  | cons value values inductionHypothesis =>
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        Fin.sum_univ_succ, inductionHypothesis]
      rfl

/-! ## §1 The restriction seam, at PCPP coordinates -/

/-- **The restriction seam.**  Each recovered PCPP coordinate is one linear
polynomial in supplier circuits at arity `n`.  This is the only assumption made
about the guessed proof. -/
def CoordinateExpands {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (pcpp : PointwisePCPP circuit) (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1) : Prop :=
  ∀ (input : BitInput n)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)),
      (coordinate j).value evaluate input = proofValue input j

/-! ## §2 The site polynomials, one per PCPP clause address -/

/-- The validity polynomial of one recovered coordinate: the paper's
`(Enc_s - T_ij)^2` on a systematic coordinate and `T_ij^2 (1-T_ij)^2` on an
auxiliary one. -/
noncomputable def coordinatePenalty {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    CircuitPolynomial Atom 4 :=
  Fin.addCases
    (fun index =>
      (systematicValidityPolynomial (systematicAtom index)
        (coordinate (Fin.castAdd pcpp.auxiliaryBits index))).weaken (by omega))
    (fun index =>
      auxiliaryValidityPolynomial
        (coordinate (Fin.natAdd pcpp.systematicBits index)))
    j

/-- The penalty site: both charged coordinates of one clause address, carrying
the schedule's own `divisor .penalty = 2`. -/
noncomputable def penaltySite {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  CircuitPolynomial.scale (1 / 2)
    ((coordinatePenalty pcpp coordinate systematicAtom
        (literalIndex (pcpp.clauses i).left)).add
      (coordinatePenalty pcpp coordinate systematicAtom
        (literalIndex (pcpp.clauses i).right)))

/-- The second-moment site: the paper's `Q_ij = T_ij^2` on the left occurrence
of one clause address. -/
noncomputable def momentSite {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  (secondMomentPolynomial
    (coordinate (literalIndex (pcpp.clauses i).left))).weaken (by omega)

/-- The clause site: the paper's `F_i = Cons_i(T_i1, T_i2)`, the degree-two
arithmetization of one indexed clause. -/
noncomputable def clauseSite {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  (clausePolynomial (literalNegated (pcpp.clauses i).left)
    (literalNegated (pcpp.clauses i).right)
    (coordinate (literalIndex (pcpp.clauses i).left))
    (coordinate (literalIndex (pcpp.clauses i).right))).weaken (by omega)

/-- **The site polynomial of one grouped phase at one PCPP clause address.**
The site index is `Fin (2 ^ pcpp.clauseBits)`; there is no other site index. -/
noncomputable def sitePolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (i : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  match ph with
  | .penalty => penaltySite pcpp coordinate systematicAtom i
  | .moment => momentSite pcpp coordinate i
  | .clause => clauseSite pcpp coordinate i

/-- **The phase polynomial.**  The uniform average of the site polynomials over
the PCPP clause addresses. -/
noncomputable def phasePolynomial {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom) :
    CircuitPolynomial Atom 4 :=
  CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
    (polynomialFinsetSum (univ : Finset (Fin (2 ^ pcpp.clauseBits)))
      (sitePolynomial ph pcpp coordinate systematicAtom))

/-! ## §3 The per-site quantity, and the site value theorem -/

/-- The real quantity one site contributes, in the schedule's own language and
already divided by the schedule's `divisor`. -/
noncomputable def siteQuantity {n : ℕ} {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (input : BitInput n)
    (v : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (i : Fin (2 ^ pcpp.clauseBits)) : ℝ :=
  match ph with
  | .penalty =>
      (2 : ℝ)⁻¹ *
        (validityPenalty
            (systematicConstraint pcpp input
              (literalIndex (pcpp.clauses i).left))
            (v (literalIndex (pcpp.clauses i).left)) +
          validityPenalty
            (systematicConstraint pcpp input
              (literalIndex (pcpp.clauses i).right))
            (v (literalIndex (pcpp.clauses i).right)))
  | .moment => (v (literalIndex (pcpp.clauses i).left)) ^ 2
  | .clause => clauseRealValue (pcpp.clauses i) v

theorem coordinatePenalty_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n} (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (input : BitInput n)
    (j : Fin (pcpp.systematicBits + pcpp.auxiliaryBits)) :
    (coordinatePenalty pcpp coordinate systematicAtom j).value evaluate input =
      validityPenalty (systematicConstraint pcpp input j)
        (proofValue input j) := by
  refine Fin.addCases ?_ ?_ j
  · intro index
    simp [coordinatePenalty, systematicConstraint, hcoordinate input,
      hsystematic, validityPenalty, systematicPenalty]
  · intro index
    simp [coordinatePenalty, systematicConstraint, hcoordinate input,
      validityPenalty, booleanityPenalty]

/-- **One site, evaluated at one PCPP input, is the schedule's own per-site
quantity.** -/
theorem sitePolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (input : BitInput n) (i : Fin (2 ^ pcpp.clauseBits)) :
    (sitePolynomial ph pcpp coordinate systematicAtom i).value evaluate input =
      siteQuantity ph pcpp input (proofValue input) i := by
  cases ph with
  | penalty =>
      show (penaltySite pcpp coordinate systematicAtom i).value evaluate input = _
      rw [penaltySite, CircuitPolynomial.scale_value,
        CircuitPolynomial.add_value,
        coordinatePenalty_value pcpp evaluate proofValue coordinate hcoordinate
          systematicAtom hsystematic input,
        coordinatePenalty_value pcpp evaluate proofValue coordinate hcoordinate
          systematicAtom hsystematic input]
      show ((1 / 2 : ℚ) : ℝ) * _ = (2 : ℝ)⁻¹ * _
      norm_num
  | moment =>
      show (momentSite pcpp coordinate i).value evaluate input = _
      rw [momentSite, CircuitPolynomial.weaken_value,
        secondMomentPolynomial_value, hcoordinate input]
      rfl
  | clause =>
      show (clauseSite pcpp coordinate i).value evaluate input = _
      rw [clauseSite, CircuitPolynomial.weaken_value, clausePolynomial_value,
        hcoordinate input, hcoordinate input]
      rfl

/-- The phase polynomial at one PCPP input is the uniform average of its sites'
quantities. -/
theorem phasePolynomial_value {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input)
    (input : BitInput n) :
    (phasePolynomial ph pcpp coordinate systematicAtom).value evaluate input =
      𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
        siteQuantity ph pcpp input (proofValue input) i := by
  rw [phasePolynomial, CircuitPolynomial.scale_value,
    polynomialFinsetSum_value]
  rw [Finset.sum_congr rfl fun i _ =>
    sitePolynomial_value ph pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic input i]
  rw [Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ, Fintype.card_fin]
  push_cast
  ring

/-! ## §4 The exactness theorems -/

/-- The grouped phase mean is the double average of the per-site quantities.
This is `penalty_mean` / `moment_mean` / `clause_mean` unfolded once. -/
theorem mean_eq_expect {n : ℕ} {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ) :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      𝔼 input : BitInput n,
        𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
          siteQuantity ph pcpp input (proofValue input) i := by
  cases ph with
  | penalty =>
      rw [CloseoutRowsOriginalSchedule.penalty_mean, aggregateClausePenaltyMean]
      have hinner : ∀ input : BitInput n,
          (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
              siteQuantity .penalty pcpp input (proofValue input) i) =
            (2 : ℝ)⁻¹ *
              totalClausePenaltyMean pcpp input (proofValue input) := by
        intro input
        show (𝔼 i ∈ (univ : Finset (Fin (2 ^ pcpp.clauseBits))),
            (2 : ℝ)⁻¹ * (_ + _)) = _
        rw [← Finset.mul_expect, totalClausePenaltyMean, clausePenaltyMean,
          clausePenaltyMean, ← Finset.expect_add_distrib]
      rw [Finset.expect_congr rfl fun input _ => hinner input,
        ← Finset.mul_expect]
      ring
  | moment =>
      rw [CloseoutRowsOriginalSchedule.moment_mean,
        CompetitorSourceAverage.leftSecondMoment, ← Finset.univ_product_univ,
        Finset.expect_product]
      exact Finset.expect_congr rfl fun input _ =>
        Finset.expect_congr rfl fun i _ => rfl
  | clause =>
      rw [CloseoutRowsOriginalSchedule.clause_mean, aggregateClauseMean]
      exact Finset.expect_congr rfl fun input _ => rfl

/-- **THE EXACTNESS THEOREM (paper C.10).**  The grouped phase mean of the
paper's three estimated reals IS the exact mean of a degree-four circuit
polynomial: a finite sum of `coefficient * conjunctionProbability`, one
AND-four supplier call per monomial.  A pure identity -- there is no error
term. -/
theorem mean_eq_exactMean {Atom : Type} {n : ℕ} {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input) :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      (phasePolynomial ph pcpp coordinate systematicAtom).exactMean evaluate := by
  rw [CircuitPolynomial.exactMean_eq_uniformMean, CircuitPolynomial.uniformMean,
    mean_eq_expect ph pcpp proofValue]
  exact Finset.expect_congr rfl fun input _ =>
    (phasePolynomial_value ph pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic input).symm

/-- **The expansion, fully unfolded** -- literally the `hexpansion` field of
`Realizes`: a `Finset`-indexed sum of `coefficient * conjunctionProbability`,
with `index = univ` over the monomial positions. -/
theorem mean_eq_sum_conjunctionProbability {Atom : Type} {n : ℕ}
    {circuit : BooleanCircuit n}
    (ph : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (evaluate : Atom → BitInput n → Bool)
    (proofValue :
      BitInput n → Fin (pcpp.systematicBits + pcpp.auxiliaryBits) → ℝ)
    (coordinate :
      Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
        CircuitPolynomial Atom 1)
    (hcoordinate : CoordinateExpands pcpp evaluate proofValue coordinate)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (hsystematic : ∀ index input,
      evaluate (systematicAtom index) input =
        parityOn (pcpp.systematicSupport index) input) :
    CloseoutRowsOriginalSchedule.mean ph pcpp proofValue =
      ∑ i : Fin (phasePolynomial ph pcpp coordinate
            systematicAtom).monomials.length,
        (((phasePolynomial ph pcpp coordinate
            systematicAtom).monomials[i].coefficient : ℚ) : ℝ) *
          conjunctionProbability evaluate
            (phasePolynomial ph pcpp coordinate
              systematicAtom).monomials[i].factors := by
  rw [mean_eq_exactMean ph pcpp evaluate proofValue coordinate hcoordinate
      systematicAtom hsystematic, CircuitPolynomial.exactMean]
  exact listSum_eq_finsetSum _ _

end NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
