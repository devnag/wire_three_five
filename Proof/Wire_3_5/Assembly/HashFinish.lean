import Proof.Wire_3_5.Assembly.HashStage1
import Proof.Wire_3_5.Primitive.SeedFix.TS4W
import Proof.Wire_3_5.Primitive.Writers.HashLeaf4
import Proof.Wire_3_5.UnionMachine.FiltPipeLe
import Proof.Wire_3_5.UnionMachine.FsSpec
import Proof.Wire_3_5.UnionMachine.WalkStage

/-!
# HASH writer: the leaf (finish term)

The hash writer at every literal set and every writer-side `PreLinkT` (P3:2220-2226, 3068-3084): `hashLeaf4`
applied to the extended data stage `thrStage4U`, C6's walk bank and FILTER setup, the FILTER-pipe bound `filtPipe_le2` and the THR number sizes `thrNumsPoly`.

Paper quantity of the main type: `HashLeafJ2 l`, the hash writer of the seed-fix stage.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.HashFinish

open NearCubicWires.WireExponent3_5

/-- **The HASH writer leaf.** -/
noncomputable def hashFinal : HashStage1.StageT :=
  fun l _ => PrimAsm.HashLeaf.hashLeaf4 l (PrimT.TS4.thrStage4U l) UnionMachine.WalkStage.walkBank
    (UnionMachine.FsSpec.fsSpec UnionMachine.WalkStage.walkBank) UnionMachine.FiltPipeLe.filtPipe_le2
    (PrimT.W6.thrNumsPoly l)

end NearCubicWires.WireExponent3_5.HashFinish
