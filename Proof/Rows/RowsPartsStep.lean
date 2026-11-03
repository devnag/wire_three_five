import Proof.Rows.RowsCompleteBank

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsConstruction.PartsStep
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairOrdinary.RecoveryRootRound
open NearCubicWires.RepairSource.VerifierDecoding NearCubicWires.RepairRepresentation
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierPrime
open NearCubicWires.P1Closure NearCubicWires.RepairOrdinary.CloseoutRowsEstimator
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open RowsConstruction.BaseLayout RowsConstruction.MaskStage RowsConstruction.CompleteWork
  RowsConstruction.CompleteRow RowsConstruction.CompleteBank
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The C3 bridge -/

section Bridge

end Bridge

/-! ## 2. The `Parts` choices: row-level ports and the Header reserve -/

def reserveOf (caps : RowCaps) (k : Fin 440) : Nat := by
  classical
  exact if PCJ45bee56da9f34d5a_HeaderErase.retained k then 0 else 2*caps.headerFuel

/-! ## 3. The row-level premises from `RowCaps.Good` -/

section RowLevel

end RowLevel

/-! ## 4. The resident C5 / mode words (`C5Ready`, supplied by RX's initializer) and the uniform fuel -/

/-! ## 5. The per-row step, THR and SYM -/

section Core

end Core

/-! ## 6. The restatement at `Row.headerOutH/A → Row.frameInH/A` (the `Parts.hstep` shape) -/

end
end RowsConstruction.PartsStep
