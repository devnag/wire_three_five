import Proof.CaseAnalysis.FinalRealizes
import Proof.Supplier.SupplierEstimator

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

/-- **The supplier.**  The rows' canonical rational output at arity `arity`. -/
noncomputable def rowSupplier {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) : ℚ :=
  decodeSupplierRational (rows.outputCode ⟨arity, circuits⟩)

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

/-- **The `hsupplier` bridge S1 needs.**  `count / denominator` IS the
supplier's answer, so a record stream carrying `rowAnswer` over
`rowDenominator` `Calls` this supplier. -/
theorem rowSupplier_eq_ratio {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) :
    ((rowAnswer rows arity circuits : ℚ) /
        (rowDenominator rows arity circuits : ℚ)) =
      rowSupplier rows arity circuits := by
  rw [rowSupplier, FourfoldRowPreprocessor.outputCode,
    FiniteRowAggregation.decode_outputCode]
  rw [rowAnswer, rowDenominator]
  congr 1
  rw [FiniteRowAggregation.sampleCount, Fintype.card_fin, card_bitInput]

/-! ## §2 `hpoint` -/

/-- **The supplier answers every AND-four call within the rows' failure.**
Paper C.10.1: the machine "estimates `mu = E_{i,u} F_i(u)` by expanding it into
AND-four supplier calls"; this is the per-call guarantee for one such call, and
the `u`-average lives entirely inside `conjunctionProbability`. -/
theorem rowSupplier_error_le {Circuit : CircuitFamily}
    {evaluate : {q : ℕ} → Circuit q → BitInput q → Bool}
    (rows : FourfoldRowPreprocessor Circuit evaluate) (arity : ℕ)
    (circuits : List (Circuit arity)) :
    |((rowSupplier rows arity circuits : ℚ) : ℝ) -
        conjunctionProbability evaluate circuits| ≤
      rows.failure ⟨arity, circuits⟩ := by
  have hdecode := rows.decode_outputCode ⟨arity, circuits⟩
  have haccurate := rows.accurate ⟨arity, circuits⟩
  rw [rowSupplier, hdecode]
  exact haccurate

/-! ## §3 The two production families, at the failure the paper names

`symmetricFourfoldRows` is `thm:supplier-fixed`'s row family (paper.tex:721,
carried exponent 5) and `thresholdFourfoldRows` is `thm:supplier-inverse`'s
(paper.tex:701, exponent 9).  Both read their failure straight off the
requested reciprocal accuracy. -/

/-! ## §4 `hbudget` -/

/-! ## §5 The fused deliverable: `Realizes` with both supplier fields closed -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
