import Proof.CaseAnalysis.FinalExactness

/-!
# P3b — C.10.2 stability: the propagated estimation error

Paper C.10.2 (paper.tex:4151): "Choose every propagated estimation error below
`eps_est := min{zeta, (c_p - s_p)/20}`", which is
`CompetitorRationalGap.estimationTolerance constants (zeta constants)`.

The propagation ledger is `failure * coefficientMass`: a supplier that answers
every AND-four call within `failure` moves the estimated phase mean by at most
`failure` times the expansion's coefficient mass.  `estimate_stable` below is
that bound stated against `CloseoutRowsOriginalSchedule.mean`, the paper's own
grouped quantity, so `failure * mass <= estimationTolerance` is exactly the
`hbudget` field of `Realizes`.

`phaseMassCap` is the coefficient-mass ledger of the three phases in terms of
the per-coordinate mass.  It is a DERIVED bound, not a free constant: every
term comes from a `coefficientMass` lemma of `ComponentwisePolynomial`
(`systematicValidityPolynomial`, `auxiliaryValidityPolynomial`,
`secondMomentPolynomial`, `clausePolynomial`), matching the manuscript's
`q^{rho_coef}` coefficient-mass envelope (paper.tex:1411).
-/

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability

open Finset
open scoped BigOperators
open NearCubicWires
open NearCubicWires.AggregateClauseExpansion
open NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.ComponentwisePolynomial
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §0 `Finset` presentations of the two list-shaped ledgers -/

/-! ## §1 The coefficient-mass ledger of the three phases -/

/-! ## §2 The propagated estimation error -/

end NearCubicWires.RepairOrdinary.CloseoutFinalC10Stability
