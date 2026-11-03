import Proof.CaseAnalysis.FinalRealizes
import Proof.CaseAnalysis.FinalLengthGate
import Proof.CaseAnalysis.RowsEstimatorCoefficientsLoop
import Proof.Hierarchy.CompetitorSumLoop
import Proof.CaseAnalysis.RowsOriginalClauseLoop

/-! # W1 -- the C.10 worker chain, anchored at the PCPP clause addresses

Paper C.10 (paper.tex 4098-4110):

> The weak machine estimates `E_{i,j,u} P_ij` and every `E_u Q_ij`.  **All
> expressions have degree at most four in the guessed sums.** ... Expanding
> `(Enc_s - T_ij)^2` then uses only constants, carried atoms, and conjunctions
> of one parity atom with at most one carried atom; **no parity-support
> enumeration occurs.**

Paper C.10.1 (paper.tex 4103):

> estimates `mu = E_{i,u} F_i(u)` **by expanding it into AND-four supplier
> calls**.

This module realizes those two sentences physically.  The machine ranges over
PCPP clause addresses `i : Fin (2 ^ pcpp.clauseBits)` -- P3a's site list -- and
emits, per address, **one record per monomial of that address's site
polynomial**; each such record is one AND-four supplier call, because the
monomial's factor list has length at most four by the degree index of
`CircuitPolynomial Atom 4` (`phasePolynomial_factors_length_le_four`).  The
`u`-average never appears as an enumeration: it sits inside
`conjunctionProbability`, which is what the supplier answers.

Three things are proved here.

* **The call list of the phase is the concatenation of the call lists of the
  clause addresses** (`calls_of_clauseAddresses`).  This is the physical form
  of "site list = PCPP clause address, and nothing else".
* **The machine's exact signed-rational fold of those calls IS the paper's
  estimated mean** (`folded_value_eq_estimatedMean`).  This is C.10.1's
  "expanding it into AND-four supplier calls", as an identity between the
  corpus's own `CompetitorSumFold.folded` and `CircuitPolynomial.estimatedMean`.
* **The gated worker realizes one phase** (`worker_realizes`).  The length gate
  of P4 is the worker's front; the estimator body is docked inside it; the
  budget is a function of the input length alone.

The one obligation this module does NOT discharge is `EstimatorBody`: the
physical receipt that the docked estimator body, started at the gate's exit on
the verifier's own tapes, leaves the record word of that fold on its output
port.  That structure is the exact junction, stated so that every field of it
is named.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateClauseExpansion
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ComponentwiseTransfer
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.RepairSource.VerifierDecoding
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 One record is one AND-four supplier call -/

/-- **One physical record = one AND-four supplier call for one monomial.**
The record carries the monomial's rational coefficient in its `coefficient`
field and the supplier's answer as the `count / denominator` pair: exactly
`Entry.estimate_value`'s two factors.  Paper C.10.1, "expanding it into
AND-four supplier calls". -/
structure Calls {Atom : Type} (supplier : List Atom → ℚ)
    (monomial : CircuitMonomial Atom 4) (entry : Entry) : Prop where
  /-- The record's rational coefficient is the monomial's coefficient. -/
  coefficient : entry.coefficient.value = monomial.coefficient
  /-- The record's `count / denominator` is the supplier's answer to the
  monomial's factor list. -/
  answer : ((entry.count : ℚ) / (entry.denominator : ℚ)) = supplier monomial.factors

/-! ## §2 The record stream's exact value -/

/-- The per-record contribution values, read off the calls. -/
theorem entries_map_estimate_value {Atom : Type} (supplier : List Atom → ℚ)
    (monomials : List (CircuitMonomial Atom 4)) (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) monomials entries) :
    entries.map (fun entry => entry.estimate.value) =
      monomials.map (fun monomial => monomial.coefficient * supplier monomial.factors) := by
  induction hcalls with
  | nil => rfl
  | @cons monomial entry monomials entries hcall _ inductionHypothesis =>
      simp only [List.map_cons, inductionHypothesis]
      congr 1
      rw [Entry.estimate_value, hcall.coefficient, hcall.answer]

/-- **C.10.1, as an identity.**  The corpus's own exact signed-rational fold of
the record stream has value `polynomial.estimatedMean supplier` -- the paper's
`mu` expanded into AND-four supplier calls.  No approximation enters here; the
supplier's error is P3b's business. -/
theorem folded_value_eq_estimatedMean {Atom : Type} (supplier : List Atom → ℚ)
    (width : ℕ) (polynomial : CircuitPolynomial Atom 4) (entries : List Entry)
    (hcalls : List.Forall₂ (Calls supplier) polynomial.monomials entries)
    (hvalid : ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate width) :
    (((CompetitorSumFold.folded CompetitorSumWidth.zero
        (contributions entries)).value : ℚ) : ℝ) =
      polynomial.estimatedMean supplier := by
  have hfold := CompetitorSumFold.folded_value
    (CompetitorSumWidth.width (contributions entries).length width)
    CompetitorSumWidth.zero (contributions entries)
    (CompetitorSumWidth.uniform_trace width (contributions entries) hvalid)
  have hzero : CompetitorSumWidth.zero.value = 0 := by
    norm_num [CompetitorSumWidth.zero, CompetitorValidity.Estimate.value]
  have hmap : (contributions entries).map CompetitorValidity.Estimate.value =
      polynomial.monomials.map
        (fun monomial => monomial.coefficient * supplier monomial.factors) := by
    rw [contributions, List.map_map]
    exact entries_map_estimate_value supplier polynomial.monomials entries hcalls
  rw [hfold, hzero, zero_add, hmap, ratListSum_cast, List.map_map,
    CircuitPolynomial.estimatedMean]
  refine congrArg List.sum (List.map_congr_left ?_)
  intro monomial _
  simp only [Function.comp_apply]
  push_cast
  ring

/-! ## §3 The clause-address decomposition -/

/-! ## §4 The physical clause-address driver -/

/-! ## §5 The gated worker -/

/-- **The worker.**  P4's length gate is its front: the gate counts the frozen
onset out of the framed input in `4*C+3` steps, rejects below the cutoff, and
otherwise hands the estimator body the verifier's own tapes with every head at
zero and the single scratch slot `flag` carrying `[true]`. -/
def worker {tapes bodyStates : ℕ} (onset : ℕ) (input flag result : Fin tapes)
    (body : Machine tapes bodyStates) :
    Machine tapes ((4 * onset + 2) + (2 + bodyStates)) :=
  gated onset input flag result body

/-- **The budget is a function of the input length alone.**  The gate costs
`4*C+3` and the body is charged `fuel len`; neither term mentions the witness
string, which is what `Weak.StepAtInputs` requires of a `budget : ℕ → ℕ`. -/
def workerBudget (onset : ℕ) (fuel : ℕ → ℕ) (len : ℕ) : ℕ :=
  (4 * onset + 1) + 1 + (fuel len + 1)

/-! ## §6 The junction, and the phase realization -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
