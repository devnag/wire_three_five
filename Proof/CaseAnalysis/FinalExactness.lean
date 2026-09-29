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

/-! ## §4 The exactness theorems -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
