import Proof.Wire_3_5.Primitive.SeedFix.C4SymLfCBase
import Proof.Wire_3_5.FinalPass.SymBuildBase
import Proof.Wire_3_5.FinalPass.SampPad2
import Proof.Wire_3_5.Primitive.Writers.C3W3BudgetBase
import Proof.Wire_3_5.Primitive.Writers.C3WBudgetABase
import Proof.Wire_3_5.Primitive.SeedFix.C3ReqIface

/-!
# The c4 leaf's SYM mode, closed

The SYM third of the seed-fixing leaf, with every input supplied by a verified producer: the assembly `symLeafC4`
at the v7 builder `SymFr.symFreeOk`, the C3 request writer v3 `c3ReqLeaf3`,
and the padded batch's evaluation lemma `SampShape.chV_pad_eval`. The Williams algorithm
`wa` stays a parameter; the c4 assembly picks it from the williams literal by choice.

Paper quantity of the main type: `C4K.SymLeafC4 l`, the SYM stage of `lem:primitive`'s seed fixing
(P3:3011-3016, 3165-3175).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.C4SymClosed

open NearCubicWires.WireExponent3_5

/-- The padded batch evaluates as the empty one: the lemma in the `PadEval` shape. -/
theorem padEval : PrimT.C4SymLf.PadEval := fun P nT b p' v => FinalPass.SampShape.chV_pad_eval P nT b p' v

end NearCubicWires.WireExponent3_5.C4SymClosed
