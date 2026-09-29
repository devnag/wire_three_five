import Proof.Wire_3_5.Assembly.HashStage1
import Proof.Wire_3_5.Primitive.Writers.HashLeaf4

/-!
# HASH writer, module stage 2

The second verified block for the hash writer's finish: `hashLeaf4` with its closure beyond stage 1.
It proves nothing new: the node's target passes through unchanged under the alias `StageT`, and the block becomes
context, so the final finish ships only the data-stage producer and the leaf term.

Paper quantity of the main type: `HashLeafJ2 l`, the hash writer of the seed-fix stage (P3:2220-2226, 3068-3084).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.HashStage2

open NearCubicWires.WireExponent3_5

/-- The HASH writer leaf, unchanged (an alias). -/
abbrev StageT : Type := HashStage1.StageT

def pass (h : StageT) : HashStage1.StageT := h

end NearCubicWires.WireExponent3_5.HashStage2
