import Proof.CaseAnalysis.FinalRealizes

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Realizes
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1 The supplier: a row preprocessor's rational answer at one arity

`Realizes.estimate` wants a `List Atom -> Q`.  A `FourfoldRowPreprocessor` is
exactly that at each fixed arity, through the corpus's own canonical output
code -- so the supplier is READ OFF the rows rather than assumed. -/

/-- The supplier's answer as a COUNT, the shape S1's `Calls` record carries. -/
def rowAnswer {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) : ℕ :=
  (rows.aggregation ⟨arity, circuits⟩).acceptanceCount

/-- The supplier's denominator, which is per-request: `rowCount * 2 ^ arity`. -/
def rowDenominator {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) : ℕ :=
  rows.rowCount ⟨arity, circuits⟩ * 2 ^ arity

/-! ## §2 `hpoint` -/

/-! ## §3 The two production families, at the failure the paper names

`symmetricFourfoldRows` is `thm:supplier-fixed`'s row family (paper.tex:721,
carried exponent 5) and `thresholdFourfoldRows` is `thm:supplier-inverse`'s
(paper.tex:701, exponent 9).  Both read their failure straight off the
requested reciprocal accuracy. -/

/-! ## §4 `hbudget` -/

/-! ## §5 The fused deliverable: `Realizes` with both supplier fields closed -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
