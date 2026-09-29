import Proof.Wire_3_5.FinalPass.Stage9
import Proof.Wire_3_5.UnionMachine.NumsN5
import Proof.Wire_3_5.Primitive.SeedFix.TplLenC5

/-!
# The final-pass leaf

Root's closure join `finalPassClose10` at SW's numbers part: `swN` over the
SYM front and the post-front program `postN`/`postRun`, with the template-length program `tplLenW` and
its interface `tplLen_iface : TplIface tplKt tplEt tplLenW` (over the TplLenA/B) at `x = DT + 8`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPassFinal

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split

/-- **The final-pass leaf** at every literal instance. -/
noncomputable def finalPassFinal : FinalPassStage9.StageT :=
  FinalPass.Close10.finalPassClose10 (fun l => UnionMachine.NumsA.swN (UnionMachine.DataDock.DT + 8) le_rfl l
    PrimT.TplLenC.tplKt PrimT.TplLenC.tplEt (fun O W RM RB RJ RL RT => PrimAsm.TplLen.tplLenW O W RM RB RJ RL RT)
    PrimT.TplLenC.tplLen_iface)

end NearCubicWires.WireExponent3_5.FinalPassFinal
