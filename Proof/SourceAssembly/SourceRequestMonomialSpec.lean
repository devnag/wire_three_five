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

end site

end NearCubicWires.SourceRequest.MonomialSpec

