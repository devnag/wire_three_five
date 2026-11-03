import Proof.SourceAssembly.SourceRequestFactorLoop

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.MonomialSpec
open NearCubicWires NearCubicWires.ComponentwisePolynomial

section lists

end lists

section poly

end poly

/-! ## The site's monomial count `N` (what `nT` receives), per phase

`N` depends only on the two queried coordinates' term counts `JL`, `JR`, the two literal signs (clause phase) and
whether each literal index is systematic (penalty phase: `coordinatePenalty` is `Fin.addCases`). -/

section site
open NearCubicWires.RepairOrdinary NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness
open NearCubicWires.ComponentwiseBranchExtraction NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule
open NearCubicWires.SourceInterfaces NearCubicWires.LocalBitMultitape

/-- One side's validity-block count: systematic `1 + J + J²`, auxiliary `J² + J³ + J⁴`. -/
def penLen (sys : Bool) (J : Nat) : Nat :=
  if sys then 1 + (J + J * J) else J * J + (J * J * J + J * J * (J * J))

end site

end NearCubicWires.SourceRequest.MonomialSpec

