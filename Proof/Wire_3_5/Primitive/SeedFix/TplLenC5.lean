import Proof.Wire_3_5.Primitive.SeedFix.TplLenC4
import Proof.Wire_3_5.UnionMachine.NumsN3

/-! # TplLenC, part 5: the template length program docked at the interface

**`tplLen_iface`**: `UnionMachine.NumsA.TplIface tplKt tplEt (fun O W RM RB RJ RL RT => tplLenW O W RM RB RJ RL RT)`
, the argument SWn's phase Q consumes (`invQ_step`, `tpls_run`): `RT` ends at `tplNum M B L`, the
stage-5 template's length.

Paper quantity of the main type: `tplNum M B L = |levelWord M J W (L-rows)|` (list:base P3:1449-1477, the SYM call
numbers P3:3170-3178). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.TplLenC
open NearCubicWires NearCubicWires.WireExponent3_5

/-- **The template length program meets `TplIface tplKt tplEt`.** -/
theorem tplLen_iface :
    UnionMachine.NumsA.TplIface tplKt tplEt (fun O W RM RB RJ RL RT => PrimAsm.TplLen.tplLenW O W RM RB RJ RL RT) :=
  tplLen_spec

end NearCubicWires.WireExponent3_5.PrimT.TplLenC
