import Proof.SourceAssembly.SourceRequestMonomialSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.SelSpec
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.MonomialSpec


section real

end real

/-! ## The three site lists, symbolically -/

section site

end site

section site2
open NearCubicWires.RepairOrdinary.CloseoutFinalC10Exactness NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape

end site2

end NearCubicWires.SourceRequest.SelSpec

