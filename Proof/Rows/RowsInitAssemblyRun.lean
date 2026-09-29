import Proof.Rows.RowsInitAssemblyWork

/-! # Rows initializer: the `InitHole'` assembly, part 2 — the whole run to `Family.entry`'s blocks

**Consumer.** `InitHole'.initial` (`Proof/Rows/RowsFinalNE.lean`) and `InitHole'.c5` (`:50`): the final bank of ONE run of `initM` from
`rowPublicInput`, blockwise equal to `Family.entry`'s tapes (Header block `headerBank … 0`, Frame block `frameBank caps []`, work block
`workBank … (baseOf … at the bank's OWN pub/init/rcp) … 0`, counter `word |rows|`), heads `hFin`, and `C5Ready` on its `init` block
(nonempty families).

**Proof.** `work_run` (part 1) ; RX's `Global.work_dock` ; `tailIn_of` (the tail's entry facts from the work phase's `Side`, `baseOf`'s
`rowp` words and `rowPublicInput`) ; RX's `Global.tail_ne` / `tail_e` ; `TailOut.low` transports `C5Ready` (init ports `< 146 < iD`).

**Paper.** `paper.tex:1190-1212`.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsConstruction.InitAssembly
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.PacketFamilyParent
open RowsInit.Global
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. Block facts -/

section Blocks

end Blocks

/-! ## 2. The tail's entry facts from the work phase -/

section Tail


end Tail

/-! ## 3. The whole run -/

section Run

end Run

end
end RowsConstruction.InitAssembly
