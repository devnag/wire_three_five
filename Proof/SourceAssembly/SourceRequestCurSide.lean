import Proof.SourceAssembly.SourceRequestCurWriter

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurSide
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceFactorSel.Count (mulM wordM mul_step word0_step read_flag)
noncomputable section

/-! ## Generic helpers: length bookkeeping, interval frames, the `CursorOut` builder -/

/-! ## The side contract -/

/-! ## The systematic side (`s = true`) -/



/-! ## The auxiliary side (`s = false`) -/




/-! ## One side: the aux flag selects the decode -/

end
end NearCubicWires.SourceRequest.CurSide

