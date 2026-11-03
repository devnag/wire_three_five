import Lean
import Proof.Wire_3_5.FinalPass.Core15
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Core11
import Proof.Wire_3_5.FinalPass.Core12
import Proof.Wire_3_5.FinalPass.Core13
import Proof.Wire_3_5.FinalPass.Core14
import Proof.Wire_3_5.FinalPass.Core9
import Proof.Wire_3_5.FinalPass.CoreIfaceM
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg2
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5Seam2
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.Core15Base


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core, part 16: the core half's run (P3:3044-3048, 3170-3181)

**`core_run`**: from the THR half's exit (`ThrExit2`), every head at `0`, the core half's machine `coreM` reaches the
front's exit `exitA` (the words of `frontWordsW2`, `Num = 0` and `Den = fpDen` in `Tf`-bit binary, every other tape
`0^{blOf2}`), every head at `0`, within `coreCost`: the count, the mode, parts A and B, the numbers, the SYM branch,
the final pad (`stage12`, `stageABN`, `stageS`, `stageF`), given the bank's register length `c = L.Kc·N^{L.Dc}`
covers `2N` and every writer's capacity and step bound.

Paper quantities: the front's words and the printed numbers' start (P3:3044-3048, 3170-3181). -/

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
