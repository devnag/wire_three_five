import Lean
import Proof.Wire_3_5.FinalPass.Core11Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Core11
import Proof.Wire_3_5.FinalPass.CoreIfaceM
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.FinalPass.Core13Base


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core, part 13: the writers' stages (P3:3044-3048, 3170-3181)

* **`stageABN`**: S4's words part A (slots `0 … 3`), part B (slots `4 … 7`) and the numbers (`tN`, `tD`) written by
  their machine writers (`wstage`), the room invariant moved to the SYM block, the reference, the mode tape and every
  other tape kept;
* **`stageS`**: the branch on the mode tape: at a SYM request the SYM words written (`SymWordsM`), at a THR request
  nothing.

Paper quantities: S4's own words, the printed numbers' start, the SYM evaluator's call words (P3:3044-3048,
3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Run

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
