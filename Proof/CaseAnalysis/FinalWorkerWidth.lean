import Proof.CaseAnalysis.FinalWorkerEmit

/-! # W1 -- the bank width of the estimator's answer

Cross-segment constraint 10 of the plan (`Realizes.hvalid : result.Valid width`)
asks W1 to settle the width at which the estimator's answer is a valid
`CompetitorValidity.Estimate`.  It is settled here, and it is not a new
constant: it is the corpus's own uniform prefix width for the call stream,
`foldWidth recordWidth entries = CompetitorSumWidth.width (#calls) recordWidth`,
which is exactly the width the fold of `RepairCloseoutFinalC10WorkerFold` runs
at.  No numeric constant is introduced.

The validity of the ANSWER is therefore not an assumption: the fold's own
width trace already carries it, because `CompetitorSumWidth.Trace` ends on the
final accumulator.  This removes a field from the `EstimatorBody` junction.
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth

open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerChain
open NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerFold
open NearCubicWires.RepairOrdinary.CloseoutRowsEstimatorCoefficients.Stream (Entry contributions)
open NearCubicWires.RepairSource.CloseoutFinal.C10LengthGate

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-- The fold's width trace ends on the final accumulator, so the answer is
valid at the trace's width. -/
theorem folded_valid (scalarWidth : ℕ) (start : CompetitorValidity.Estimate)
    (terms : List CompetitorValidity.Estimate)
    (htrace : CompetitorSumWidth.Trace scalarWidth start terms) :
    CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded start terms) scalarWidth := by
  induction terms generalizing start with
  | nil => exact htrace
  | cons term terms inductionHypothesis =>
      exact inductionHypothesis _ htrace.2.2

/-- **Constraint 10, settled.**  The estimator's answer is a valid `Estimate` at
the fold's own width; no fresh constant enters. -/
theorem answer_valid (recordWidth : ℕ) (entries : List Entry)
    (hvalid : ∀ estimate ∈ contributions entries,
      CompetitorValidity.Estimate.Valid estimate recordWidth) :
    CompetitorValidity.Estimate.Valid
      (CompetitorSumFold.folded CompetitorSumWidth.zero (contributions entries))
      (foldWidth recordWidth entries) :=
  folded_valid _ _ _ (CompetitorSumWidth.uniform_trace recordWidth
    (contributions entries) hvalid)

end NearCubicWires.RepairOrdinary.CloseoutFinalC10WorkerWidth
