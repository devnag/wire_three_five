import Proof.Rows.RowsInitLoopTable

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true

namespace RowsInit.VecDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent NearCubicWires.PacketsGlue.RequestMeta
open NearCubicWires.RepairOrdinary.RecoveryRootRound PCJd4d1d9d7d1fa4313_Production
noncomputable section

/-! ## 1. Docking a heads-`0` run into a bank with arbitrary heads elsewhere -/

theorem run_dock {t u s n : ℕ} {p : Machine t s} {tin tout : Fin t → List Bool}
    (h : Step p n (fun _ => 0) tin (fun _ => 0) tout) (sl : Fin t → Fin u) (hi : Function.Injective sl)
    (H : Fin u → ℕ) (A : Fin u → List Bool) (hH : ∀ j, H (sl j) = 0) (hA : ∀ j, A (sl j) = tin j) :
    Step (RecoveryFocus.machine sl p) n H A H (install sl A tout) :=
  (h.dock sl hi H A hH hA).congr (ExtDecompositionBatch.dockH_existing _ _ _ hH) rfl

/-! ## 2. A `VecStage` under the all-heads masked reset -/

/-! ## 3. A `VecStage` from an indexed family of word stages -/

end
end RowsInit.VecDock
