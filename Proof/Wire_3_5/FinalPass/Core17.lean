import Lean
import Proof.Wire_3_5.FinalPass.Core16
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Core11
import Proof.Wire_3_5.FinalPass.Core9
import Proof.Wire_3_5.FinalPass.CoreIfaceM
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.Core17Base


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core, part 17: the core half's cost below one power (P3:3170-3181)

With the master bound `Y = (L.Kc + 1)·N^{L.Dc}` (`N = |fpIn| + 1`, `L.Dc ≥ 1`), which covers the register length
`c = L.Kc·N^{L.Dc}`, `N` and every writer's step bound: the count's chain (**`zCost_le`**), the count (`cnt_le`), the
mode (`mode_le`), each writer's stage (`stage_le`), the final pad (`fin_le`), and **`coreCost_le`**:
`coreCost ≤ Cc0·Y`, `Cc0 = 200 + 80·Dc + 30·(nr_A + nr_B + nr_N + nr_S + L.t)`.

Paper quantity: the front's running time as a power of the input's length (P3:3170-3181). -/

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
open NearCubicWires.WireExponent3_5.FinalPass.S5T (mulCost)

section Cost

end Cost

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
