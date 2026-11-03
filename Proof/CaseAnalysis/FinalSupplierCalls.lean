import Proof.CaseAnalysis.FinalWorkerWidth
import Proof.Hierarchy.CompetitorMonomialProducts

/-! # S1 -- per-clause-address production of the AND-four supplier calls

Paper C.10.1 (paper.tex 4130):

> In addition to validity, the machine estimates `mu = E_{i,u} F_i(u)` **by
> expanding it into AND-four supplier calls**, and accepts a branch only if
> `mu~ >= theta_acc := (c_p + s_p)/2`.

Paper C.10 (paper.tex 4098-4110):

> The weak machine estimates `E_{i,j,u} P_ij` and every `E_u Q_ij`.  **All
> expressions have degree at most four in the guessed sums.** ... Expanding
> `(Enc_s - T_ij)^2` then uses only constants, carried atoms, and conjunctions
> of one parity atom with at most one carried atom; **no parity-support
> enumeration occurs.**

W1 (`RepairCloseoutFinalC10WorkerChain`) left exactly one semantic field of the
`EstimatorBody` junction open on the production side: `hcalls`, the statement
that the record stream the body emits IS the paper's expansion.  W1 reduced it,
through `EstimatorBody.ofClauseAddresses`, to the per-clause-address obligation

```
hsite : forall address, List.Forall₂ (Calls supplier)
          (scale (1/2^clauseBits) (sitePolynomial ph pcpp coordinate systematicAtom address)).monomials
          (records address)
```

This module discharges that obligation, and gives the physical receipt that
each of those calls is emitted by the corpus's own record appender.

## What a supplier call is, physically

`Calls supplier monomial entry` (W1) has two conjuncts, and the corpus's record
format has exactly two slots to carry them:

* `entry.coefficient.value = monomial.coefficient` -- the monomial's rational
  coefficient, carried as the record's signed pair with its denominator.  The
  coefficient is a datum of the PHASE and the clause's two source-specified
  signs; it contains nothing about the guessed proof, and nothing about `u`.
* `entry.count / entry.denominator = supplier monomial.factors` -- the
  supplier's answer to that monomial's at-most-four factor list, carried as the
  record's count/denominator pair.  This is the ONLY place the `u`-average
  enters, and it enters as the supplier's answer, never as an enumeration:
  `conjunctionProbability` is what the supplier estimates, and
  `Realizes.hpoint` is where its accuracy is charged.

The count/denominator shape is the corpus's own supplier answer shape.
`CloseoutRowsEstimator.WholeRetained.run` concludes

```
actual.final.tapes (recordSlot (producer a))
  = Stream.recordWord (scalarWidth (EquationRow.request row) Q) q
      (selected (CompetitorSelectedCells.cells row.odd f select)).sum denominator
```

-- one rational coefficient `q` against one selected-cell COUNT over one fixed
denominator.  `countSupplier` below is that reading, as a function of the
factor list alone: an answer channel `answer : List Atom -> ℕ` at a fixed
denominator.  Making it a function of `monomial.factors` is the whole content
of "the selected-cell count IS the supplier's answer to that monomial's
at-most-four factor list": two monomials with the same factor list get the same
answer, so the record stream is a stream of CALLS and not of free numbers.

## What is NOT claimed here

Nothing about the accuracy of `supplier`.  `Realizes.hpoint`
(`|supplier factors - conjunctionProbability evaluate factors| <= failure`) and
`Realizes.hbudget` are separately owned (P3b / the supplier ledger, f33 §9.12
constraint 20, whose donors are `estimator_symmetricRows_failure_le` and
`estimator_thresholdRows_failure_le`).  `supplier` is left a parameter here,
tied to the emitted records by `hsupplier`, precisely so that this module
cannot foreclose that obligation.

## The range

`address : Fin (2 ^ pcpp.clauseBits)` -- P3a's site list, the PCPP clause
address and nothing else.  `BitInput n` is never enumerated.  Every quantity
below is a function of the clause address and of the monomial, so the emitted
stream is indexed by clause addresses, which is what the physical driver
(`CloseoutRowsOriginalClauseLoop.run` at `N := 2 ^ pcpp.clauseBits`) ranges
over.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls

open Finset
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerEmit
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.SourceInterfaces

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The coefficient slot: one rational, exactly -/

/-- **The monomial's rational coefficient, in the record's coefficient slot.**
The corpus's signed split of a rational (`CompetitorMonomialProducts.positive`
/`negative`, the numerator's two sign parts) against the rational's own
denominator.  No rounding and no new constant: this is the identity encoding of
`ℚ` into `CompetitorValidity.Estimate`. -/
def coefficientEstimate (coefficient : ℚ) : CompetitorValidity.Estimate :=
  ⟨CompetitorMonomialProducts.positive coefficient,
    CompetitorMonomialProducts.negative coefficient, coefficient.den⟩

/-! ## §2 The supplier's answer channel -/

/-- **One monomial, one call, one record.**  The record carries the monomial's
coefficient in its coefficient slot and the supplier's answer to the monomial's
at-most-four factor list in its count/denominator slot. -/
def callEntry {Atom : Type} (answer : List Atom → ℕ) (denominator : ℕ)
    (monomial : CircuitMonomial Atom 4) : Entry :=
  ⟨coefficientEstimate monomial.coefficient, answer monomial.factors, denominator⟩

/-! ## §3 One record per monomial -/

/-- The call stream of one polynomial: one record per monomial, in order. -/
def callRecords {Atom : Type} (answer : List Atom → ℕ) (denominator : ℕ)
    (polynomial : CircuitPolynomial Atom 4) : List Entry :=
  polynomial.monomials.map (callEntry answer denominator)

/-! ## §4 The record width -/

/-- The bound on a polynomial's coefficients that the bank width has to carry. -/
def CoefficientsFit {Atom : Type} (entryWidth : ℕ)
    (polynomial : CircuitPolynomial Atom 4) : Prop :=
  ∀ monomial ∈ polynomial.monomials,
    CompetitorMonomialProducts.positive monomial.coefficient < 2 ^ entryWidth ∧
      CompetitorMonomialProducts.negative monomial.coefficient < 2 ^ entryWidth ∧
      monomial.coefficient.den < 2 ^ entryWidth

/-! ## §5 The clause address -/

/-- **The calls of one PCPP clause address.**  P3a's site polynomial at that
address, carrying the phase's uniform `1/2^clauseBits`.  The site index is the
clause address and nothing else. -/
noncomputable def siteCalls {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) : CircuitPolynomial Atom 4 :=
  CircuitPolynomial.scale (1 / (2 ^ pcpp.clauseBits : ℚ))
    (sitePolynomial phase pcpp coordinate systematicAtom address)

/-- The record stream emitted at one PCPP clause address. -/
noncomputable def siteRecords {Atom : Type} {arity : ℕ} {circuit : BooleanCircuit arity}
    (answer : List Atom → ℕ) (denominator : ℕ)
    (phase : CloseoutRowsOriginalSchedule.Phase) (pcpp : PointwisePCPP circuit)
    (coordinate : Fin (pcpp.systematicBits + pcpp.auxiliaryBits) →
      CircuitPolynomial Atom 1)
    (systematicAtom : Fin pcpp.systematicBits → Atom)
    (address : Fin (2 ^ pcpp.clauseBits)) : List Entry :=
  callRecords answer denominator (siteCalls phase pcpp coordinate systematicAtom address)

/-! ## §6 S1 -- the per-clause-address call production, with its receipt -/

/-! ## §7 The phase's whole call stream -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierCalls
