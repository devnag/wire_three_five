import Lean
import Proof.Wire_3_5.Primitive.Writers.SymLeafIface
import Proof.Wire_3_5.Primitive.Writers.PopSetupSpecB2
import Statement_Wire_3_5
import Proof.Wire_3_5.Primitive.Writers.WritersJoin


noncomputable section
set_option maxRecDepth 4096


/-! # PA2 (POP setup): the SYM writer's leaf from its producers, over `PopSetupSpecB2` (type)

`SymLeaf.SymLeafOf` with the POP setup `Q : PopSetupSpecB2 W` (the need's measure reads the row
offset `r4`, `PopSetupSpecB2`) in place of `PopSetupSpecB W`; the other producers (the walk bank, the FILTER setup,
`FiltPipeLe2`, `PopPipeLe`) as there.

* **`SymLeafOf2 l`**.

Paper quantities of the main types: the POP row's cost (list:flatten P3:1491-1498, row:sym P3:2477-2496) and the SYM
tape `symTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The SYM writer's leaf over `PopSetupSpecB2`.** -/
abbrev SymLeafOf2 (l : Literals) : Type :=
  (W : PrimT.WalkBank.WalkBankProducer) → FiltSetup.FiltSetupSpec5 W → PopSetup.PopSetupSpecB2 W →
    BudgetIface.FiltPipeLe2 → PopPipeLe → WritersJoin.SymLeafJ2 l

end NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf

end
