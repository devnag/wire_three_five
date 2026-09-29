import Proof.SourceAssembly.SourceRequestCurClausePart

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.SourceRequest.CurClause
open NearCubicWires LocalBitMultitape ExtDecompositionBatch RepairOrdinary RepairOrdinary.RecoveryRootRound
open RepairSource.VerifierDecoding
open NearCubicWires.SourceRequest.SelSpec NearCubicWires.SourceRequest.CurSpec NearCubicWires.SourceRequest.CurContract
open NearCubicWires.SourceRequest.CurPrims NearCubicWires.SourceRequest.CurComp NearCubicWires.SourceRequest.CurWriter
open NearCubicWires.SourceRequest.CurSide
open NearCubicWires.SourceFactorSel.Count (read_flag sumM wordM mulM sum_step word0_step mul_step flag_unary)
noncomputable section

/-! ## The machine -/



/-! ## Sizes -/

/-! ## The left literal (`m < aL`) -/

/-! ## The right literal (`aL ≤ m`, `m - aL < aR`) -/

/-! ## The cross block (`y = m - aL - aR < aL·aR`) -/

/-! ## Blocks 2–end (`aL ≤ m`, `aR ≤ m - aL`) -/

end
end NearCubicWires.SourceRequest.CurClause

