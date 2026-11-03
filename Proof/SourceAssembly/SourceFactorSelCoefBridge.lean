import Proof.SourceAssembly.SourceFactorSelCoefR
import Proof.SourceAssembly.SourceRequestCurSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceFactorSel.CoefBridge
open NearCubicWires NearCubicWires.ComponentwisePolynomial NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceFactorSel.CoefValue NearCubicWires.SourceFactorSel.CoefR

/-! ## At most four factors -/

/-! ## `real`'s coefficient over four slots -/

section real4
variable {Atom : Type} (T : Bool → List (CircuitMonomial Atom 1)) (e : Bool → Atom)

/-- A slot's term coefficient (`0` if the slot is not a term; never read then). -/
def tco : Option Fac → ℚ
  | some (.term r j) => (((T r)[j]?).map (fun mo => mo.coefficient)).getD 0
  | _ => 0

end real4

/-! ## The bridge -/

section bridge
open NearCubicWires.RepairOrdinary NearCubicWires.ComponentwiseBranchExtraction
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule NearCubicWires.SourceInterfaces
open NearCubicWires.LocalBitMultitape

end bridge

end NearCubicWires.SourceFactorSel.CoefBridge

