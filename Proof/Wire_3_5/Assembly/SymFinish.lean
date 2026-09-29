import Proof.Wire_3_5.Assembly.SymStage1
import Proof.Wire_3_5.Primitive.Writers.SymLeaf2
import Proof.Wire_3_5.Primitive.Writers.PopSetupReady
import Proof.Wire_3_5.UnionMachine.WalkStage
import Proof.Wire_3_5.UnionMachine.FsSpec
import Proof.Wire_3_5.UnionMachine.FiltPipeLe
import Proof.Wire_3_5.UnionMachine.PopPipeLe

/-!
# SYM writer: the leaf (finish term)

The SYM writer at every literal set and every writer-side `PreLinkT` (P3:3011-3016, 3105-3115): `symLeaf2`
applied to C6's walk bank and FILTER setup, the POP setup `popSetupSpecB2`
, the FILTER-pipe bound `filtPipe_le2` and POP-pipe bound `popPipe_le`.

Paper quantity of the main type: `SymLeafJ2 l`, the SYM writer of the seed-fix stage.
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.SymFinish

open NearCubicWires.WireExponent3_5

/-- **The SYM writer leaf.** -/
noncomputable def symFinal : SymStage1.StageT :=
  fun l _ => PrimAsm.SymLeaf.symLeaf2 l UnionMachine.WalkStage.walkBank
    (UnionMachine.FsSpec.fsSpec UnionMachine.WalkStage.walkBank)
    (PrimAsm.PopSetupReady.popSetupSpecB2 UnionMachine.WalkStage.walkBank) UnionMachine.FiltPipeLe.filtPipe_le2
    UnionMachine.PopPipeLe.popPipe_le

end NearCubicWires.WireExponent3_5.SymFinish
