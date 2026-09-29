import Mathlib
import Proof.Rows.RowsFinalNE
import Proof.Rows.RowsInitGlobal
import Proof.Rows.RowsSymLoopFan

/-! # Rows initializer: the `InitHole'` assembly, part 1 — offsets, the machine, the work phase at every request, the cost

**Consumer.** `RowsConstruction.FinalNE.InitHole' selector a printer (PrimeReserve.rpOf a)` (`Proof/Rows/RowsFinalNE.lean`), whose `initial`
is `Parts.initial`'s exact entry: ONE machine on `Fin (rowTapes printer (rowsWork NI) + 1)` from `rowPublicInput` (heads `0`) to
`Family.entry`'s heads and tapes within `rowInitBudget`, and whose `c5` is `C5Ready` on the SAME `init` block (nonempty families).

**Machine** `initM` = RX's work phase `WorkPhase.workM` docked on the work slots (`Global.work_dock`) ; RX's global tail
`Global.tailM` (Frame writer ; family counter ; Header writer | Header-277 bump). SYM branch: RF's `FrameSymInst.symSpec`; THR cascade
bounds: RF's `FrameThrBnd.thrBnd/thrBndW`; the Header writer `H : HdrSpec` (RH) is the one typed input.

**Offsets** (fixed per `a`, `H.needH`): prefix scratch from `150`, the tail's scratch `[iD, oT)` inside the work phase's blank region
`[150 + needP, oT)` (`WorkPhase.Side`), THR branch regions from `oT`, SYM branch from `oT`.

**Paper.** `paper.tex:1190-1212` (per-request initialization: the public request and caps in, every request constant computed).
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

/-! ## 1. Offsets -/

section Offsets



end Offsets

/-! ## 2. The machines -/

section Machines

end Machines

/-! ## 3. The work phase at every request -/

section Work

end Work

/-! ## 4. The initializer's cost (one uniform bound for both tail branches) -/

section Cost

end Cost

end
end RowsConstruction.InitAssembly
