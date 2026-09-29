import Proof.SourceAssembly.SourceRequestSelSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace NearCubicWires.SourceRequest.CurSpec
open NearCubicWires NearCubicWires.SourceRequest.SelSpec
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)

/-! ## Per-slot data -/



/-! ## Index algebra of the symbolic operations -/



/-! ## The moment phase: `T_L × T_L` -/

/-! ## The penalty phase: two sides, `½ · (penSide sL L ++ penSide sR R)` -/

/-! ## The clause phase: `litL ++ (litR ++ -(litL × litR))` -/

end NearCubicWires.SourceRequest.CurSpec

