import Proof.CaseAnalysis.FinalSupplierWidth

namespace NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain

open NearCubicWires
open NearCubicWires.RepairRepresentation
open NearCubicWires.RepairOrdinary.CloseoutFinalC10SupplierAccuracy
open NearCubicWires.RepairSource.CompetitorRationalGap
open NearCubicWires.SourceInterfaces
open NearCubicWires.SupplierEstimator
open NearCubicWires.SupplierPipeline

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## Section 1 The two witnesses, at the consumer's own field types -/

/-! ## Section 2 `hpoint` from the row supplier, through the floor division -/

/-! ## Section 3 `hmass` at the decoded family -/

/-! ## Section 4 `haccuracy` — the product bound, and the constraint it forces

The budget is `estimationTolerance constants (zeta constants)` and the failure
has two terms, so each term is allotted half of it.  `accuracyTarget` is the
least reciprocal accuracy that pays one term; the two inequalities of
`haccuracy_of_bounds` say that `target` and the uniform denominator both clear
it. -/

/-! ## Section 5 The constraint in closed form, for S0 / S1 / S-W's consumers -/

end NearCubicWires.RepairSource.CloseoutFinal.C10SupplierAccuracyChain
