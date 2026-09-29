import Proof.Wire_3_5.FinalPass.Close6
import Proof.Wire_3_5.FinalPass.Stage7
import Proof.Wire_3_5.FinalPass.SymF6
import Proof.Wire_3_5.FinalPass.SymFront4
import Proof.Wire_3_5.Foundations.OutMachineDPh
import Proof.Wire_3_5.Foundations.SwPartsTmpl
import Proof.Wire_3_5.Primitive.SeedFix.NwB15
import Proof.Wire_3_5.Primitive.SeedFix.SBId
import Proof.Wire_3_5.UnionMachine.NumsG2

/-!
# The final pass, module stage 8

The eighth verified block of the final pass, shipped ahead of the finish: the out machine's uniformity bundle `hU4`
and `finalPassClose5` (the output machine), the SA writer (slots 0–3, complete) and the writer combinators, the SB writer's
assembly `sbWriter` with its statements `sbIdent`/`sbOuts`, NW's phases (a), (b), (d) and its assembly `nwOf`, the
shared SYM front (`front_runA`), SW's part types and assembly `swOf` with the parts done so far (SWg; SWf's flat-table
seed loop), the data dock variants and the raw template writer, and the final join `finalPassClose6`. The finish then
ships only SB's three arithmetic statements, NW's two, SW's remaining parts and the instantiation of
`finalPassClose6`. The target passes through unchanged under the alias `StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage8

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage7.StageT

def pass (h : StageT) : FinalPassStage7.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage8
