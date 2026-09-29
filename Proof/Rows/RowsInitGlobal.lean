import Mathlib
import Proof.Packets.PacketsMetaStageRun
import Proof.Rows.RowsInitLoopTable
import Proof.Rows.RowsPartsFill

/-! # Rows initializer: the global stages on the whole row bank (work phase docked, Frame writer, counter, Header / bump)

**Consumer.** `FinalNE.InitHole'.initial` (`rows-construction-20260923/RowsFinalNE.lean`): ONE machine on
`Fin (rowTapes printer (rowsWork NI) + 1)` from `rowPublicInput` (all heads `0`) to `Family.entry`'s heads and tapes: Header block
(nonempty family: `pad (reserveOf caps k) (commonHeader k)`; empty family: the public pool word only), Header 277's head `1`,
the Frame block `RowState.frameBank caps []`, the work block `workBank … (baseOf … r) … 0`, and the family counter
`CompareMachine.word |rows|` with head `1`.

**Machine** (`initM`): the work phase `WorkPhase.workM` docked on the work slots ; the verified Frame writer
`RowsInit.frame_backing` (drivers: `rowp 0/1`, `rcp 40`; log: an `init` scratch port) ; the verified counter
`FamilyWord.word_run` docked (word on the extra tape, head `1`) ; `CloseoutRowsOriginalSwitch` on the nonempty flag (work port 150):
the Header writer `HdrSpec` (typed, RH) docked, else a one-step head bump on Header 277.

**Paper.** `paper.tex:1190-1212`. **Budget.** Work phase + `2cC+4+1+(2dR+4)` (linear) + the counter (SMALL) + Header (`HdrSpec.cost_le`)
or `1`, + `1` per composition, `2` per switch.
-/
set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace RowsInit.Global
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.ExtDecompositionBatch NearCubicWires.RepairRepresentation NearCubicWires.SupplierPipeline
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production RowsConstruction RowsConstruction.BaseLayout
open NearCubicWires.PacketsGlue.RequestMeta NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.PacketFamilyParent
attribute [local irreducible] P1TopDownPaidPayload.tapes
noncomputable section

/-! ## 1. The global ports -/

section Ports




end Ports

/-! ## 2. `baseOf` off its `init` block, per block -/

section BaseOf

end BaseOf

/-! ## 3. Global value maps -/

section Maps


end Maps

/-! ## 4. The work phase, docked -/

section Work

end Work

/-! ## 5. The Frame writer (verified `RowsInit.frame_backing`) -/

section Frame


end Frame

/-! ## 6. The family counter (verified `FamilyWord.word_run`), docked -/

section Counter



end Counter

/-! ## 7. The Header writer (typed `HdrSpec`) and the empty-family bump, docked -/

section Hdr



end Hdr

/-! ## 8. The global tail: Frame writer ; counter ; (Header writer | bump) -/

section Tail

end Tail

section TailRun

end TailRun

end
end RowsInit.Global
