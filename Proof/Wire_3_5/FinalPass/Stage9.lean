import Proof.Wire_3_5.FinalPass.Close10
import Proof.Wire_3_5.FinalPass.Stage8
import Proof.Wire_3_5.UnionMachine.NumsN4

/-!
# The final pass, module stage 9

The ninth verified block of the final pass, shipped ahead of the finish: SB's arithmetic statements (`sbP1Cost`,
`sbFieldCost`, `sbCap`), NW's phase (b) `phB` over `needB`/`vLinkB` and phase (d) `phD`, and SW's parts done so far:
the gate tables `swG`, the top tables `swT` (SWt1–SWt5), the flat tables `swf` (SymF7–SymF14), the templates `swLAll`
(SwLK/SwL/SwLA), the SYM front's `FrontOutB` (SymFront5/6) and the numbers' widths, table lengths, template-length
interface and post-front program `postN`/`postRun` (NumsN1–N4); and the closure joins `finalPassClose7`–`finalPassClose10`. The finish then ships only the template-length
program's run, SW's numbers part `swN` and the instantiation of `finalPassClose10`. The target passes through unchanged under the alias
`StageT`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassStage9

open NearCubicWires.WireExponent3_5

/-- The final-pass leaf, unchanged (an alias). -/
abbrev StageT : Type := FinalPassStage8.StageT

def pass (h : StageT) : FinalPassStage8.StageT := h

end NearCubicWires.WireExponent3_5.FinalPassStage9
