import Proof.Rows.RowsInitC5
import Proof.Packets.PacketsFieldWidth
import Proof.Packets.PacketsMetaMul
import Proof.Rows.RowsInitCount
import Proof.CaseAnalysis.FinalCompareDockLit
import Proof.PCP.ProjectionNormalizationDriverAtoms
import Proof.Packets.PacketsMetaMaps
import Proof.Rows.RowsInitHeaderWords

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.Prefix
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJd4d1d9d7d1fa4313_Production NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.BlockPlatform
open NearCubicWires.PacketFamilyParent
open RowsConstruction RowsConstruction.BaseLayout RowsInit.VecDock
open RowsInit.ThrInitRun (inst_at inst_off)
open RowsInit.ThrLoop (wp wp_val vmap vmap_val vmap_inj rw_eq)
noncomputable section

/-! ## 1. The four words -/

section Words

end Words

/-! ## 2. Slot maps (values) and their left inverses -/



section Maps




end Maps

/-! ## 3. The machine, the chained banks, the run -/

theorem rcp_val (NI : ℕ) (i : Fin 64) : (rcpPort NI i).val = 2 + NI + 8 + i.val := by
  simp [rcpPort, fixPort] <;> omega

section Banks




end Banks

section Chain

end Chain

section Run

end Run

end
end RowsInit.Prefix
