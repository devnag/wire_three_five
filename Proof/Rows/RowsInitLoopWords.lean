import Proof.Rows.RowsInitLoopFan
import Proof.MachineModel.BlockScrub
import Proof.Packets.PacketFamilyParent
import Proof.Packets.PacketsSetupWords
import Proof.Packets.PacketsWalk
import Proof.CaseAnalysis.RowsPreparationInput
import Proof.CaseAnalysis.RowsRawAtomLoop
import Proof.MachineModel.OrdinaryMatrixDimensionPrepare
import Proof.MachineModel.Semantics
import Proof.Packets.PacketsMetaBig

set_option autoImplicit false
set_option maxRecDepth 120000
set_option warningAsError true
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace RowsInit.LoopWords
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.RepairOrdinary.RecoveryExecution NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.RecoveryRootRound
open PCJ9eff70d512234a4c_Fixed PCJd4d1d9d7d1fa4313_Production
open NearCubicWires.PacketFamilyParent NearCubicWires.BlockPlatform
open NearCubicWires.PacketsGlue.RequestMeta
noncomputable section

/-! ## 1. `C·(x+1)^D` as a unary map -/

/-! ## 2. Constant stages, word-stage transport -/

/-! ## 4. The 24 words -/

section Words
open RowsConstruction RowsConstruction.BaseLayout


end Words

/-! ## 5. The vector stage: all 24 words in one fixed machine -/

end
end RowsInit.LoopWords
