import Lean
import Proof.Wire_3_5.FinalPass.Core13Base
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Core11
import Proof.Wire_3_5.FinalPass.CoreIfaceM
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core, part 14: the SYM branch (P3:3170-3181)

**`stageS`**: the branch machine reads the mode tape `[thrFlag mode]`: at a SYM request (`false`) the SYM words writer
(`SymWordsM`) runs on the last block of the room and writes the SYM slots; at a THR request (`true`) nothing runs. The
room invariant reaches the room's end; the input, the reference and every tape off the room and the SYM slots are
kept.

Paper quantity: the SYM evaluator's call words (P3:3170-3181). -/

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

section Run

end Run

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
