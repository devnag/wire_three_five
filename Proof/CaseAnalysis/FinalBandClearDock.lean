import Proof.CaseAnalysis.FinalBandRecycle

namespace NearCubicWires.RepairOrdinary.CloseoutFinalC10BandClearDock

open NearCubicWires
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.LocalBitMultitape
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCall (bank)
open NearCubicWires.RepairSource.CloseoutFinal.C10SupplierCountStage
  (scratchOf scratchOf_apply bank_scratch_apply round_step_of_dock)
open NearCubicWires.RepairOrdinary.CloseoutFinalC10BandRecycle (ZeroBand)

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option maxRecDepth 120000
set_option warningAsError true

/-! ## §1  The band slot map: three fixed tape numbers, and nothing that moves -/

/-! ## §2  The eraser's own entry and exit layouts, named -/

/-! ## §3  The dock -/

/-! ## §4  The fixed point -/

/-! ## §5  Round then clear, at the budget that makes it a constant factor -/

/-- **The budget, compiled.**  `Step.seq` charges `cost + 1 + (2*total+4)`, and
`band_length_at_cost` (`Proof/CaseAnalysis/FinalBandRecycle.lean`) pins
`total := cost + 1`.  BANDSIZE reported `3*cost+7` as arithmetic; here it is as a
theorem. -/
theorem clear_budget (cost : ℕ) : cost + 1 + (2 * (cost + 1) + 4) = 3 * cost + 7 := by omega


end NearCubicWires.RepairOrdinary.CloseoutFinalC10BandClearDock
