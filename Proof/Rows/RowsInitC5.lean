import Proof.Rows.RowsInitBinWords
import Proof.Rows.RowsInitThrInitRun
import Proof.Packets.PacketsMetaSeedCount

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.C5
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent RowsConstruction.ThrCell
open NearCubicWires.SupplierPipeline NearCubicWires.SupplierWalkBridge
open RowsConstruction RowsConstruction.BaseLayout RowsInit.VecDock RowsInit.BinWords RowsInit.LoopWords
open RowsInit.ThrInitRun (fan_dock fin_out inst_at inst_off pad_nil)
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj rw_eq)
noncomputable section

/-! ## 1. The four words -/

section Words

end Words

/-! ## 2. Slot maps -/

theorem c5_val (NI : ℕ) (i : Fin 16) : (c5Port NI i).val = 2 + NI + 594 + i.val := by
  simp [c5Port, fixPort, MT] <;> omega


section Maps




end Maps

/-! ## 3. The machine and the run -/

/-! ## 4. THR: the first key's seed is seed `0`, and `|thrSeeds| = seedCount` -/

section Thr

end Thr

end
end RowsInit.C5
