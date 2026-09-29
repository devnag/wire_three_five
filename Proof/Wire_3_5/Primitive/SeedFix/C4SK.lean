import Proof.Wire_3_5.Primitive.SeedFix.C4SJ

/-! # C4 per-call setup (item 3), part 11: the SYM setup's front, docked

P3:3119-3120 ("The algorithm receives polynomial-bit integer circuit descriptions"): from the framed request
`natWord n ++ sfx` on the stage's port `0`, the raw request, `1^n`, and three powers `C(n+1)^D` of the input length in
unary (the data stage's description bound and fill count, the numbers machine's fill count):

* `frontM`, `frontCost`, **`front_run`**.

Paper quantities of the main type: `1^n` and the unary powers of `n + 1` on their tapes. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout

/-- Tape arithmetic of the layout. -/
macro "lv" : tactic => `(tactic| (simp only [Lay.gP0, Lay.gP1, Lay.gP2, Lay.gRAW, Lay.gN1, Lay.gUL, Lay.gUD, Lay.gUW,
  Lay.gDO, Lay.gU, Lay.gW, Lay.gMA, Lay.gMB, Lay.gUU, Lay.gRR, Lay.gPRE, Lay.gPOST, Lay.gLG, Lay.oU2, Lay.oU3, Lay.oDA,
  Lay.oCP, Lay.oBG, Lay.oM1, Lay.oM2, Lay.oCU, Lay.oCR2, Lay.oC3, Lay.oLP, Fin.ext_iff, ne_eq] <;> omega))

namespace Lay

end Lay

end NearCubicWires.WireExponent3_5.PrimT.C4Set
