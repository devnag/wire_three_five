import Proof.SourceAssembly.SourceRequestCurComp
import Proof.SourceAssembly.SourceRequestCurSpec

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false

namespace NearCubicWires.SourceRequest.CurContract
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec
open NearCubicWires.RepairOrdinary.CloseoutRowsOriginalSchedule (Phase)
noncomputable section

/-! ## Ports -/


/-! ## Blank-port identities -/

/-! ## Proof helpers for cursor builders (scratch-length invariant, per-slot `∀`) -/

/-! ## Docked form -/

end
end NearCubicWires.SourceRequest.CurContract

