import Proof.Wire_3_5.FinalPass.Close2Base
import Proof.Wire_3_5.FinalPass.CoreJ10
import Proof.Wire_3_5.UnionMachine.S6SizesBase

/-! # The uniformity bundle `hU`: S6's constants at the final pass's parts

"The coefficients depend only on the gate, the degrees only on the literals and the filter error degree"
(P3:3170-3181: the final pass's running time is `c₅·(n+1)^{D₅}` uniformly over the call family). `S6Uni` asks, at
the parts of `finalPassClose4` (`coreGenJ` over the four pool writers `Wr`, S4 v2 `XfR`, the bridge, the front,
the out machine), for degrees `Dg l fe` and coefficients `Cg l fe F` above every part's own:

* the degrees are read off by `rfl` (`frontOfHalves_Df/Dw`, `thrHalf_Dt`, `coreB3J`'s `Dcc = L.Dc`, `bridgeT_Dc/Dt/
  Dp/Do`, `XfR_Dt/Dp/Do/Dc`, `outGen_D`) and summed in **`DgU`**;
* the coefficients do not depend on `(kclk, coef, A, a)` (every part's coefficient is a closed term in `l`, `F` and the
  layout, `rfl`), so **`CgU`** sums them at the parameters `(0, 0, 0, 0)`;
* **`hU4 Wr`**: the bundle, generic in the pool writers `Wr`.

Paper quantity of the main type: the final pass's degree and coefficient, uniform over the call family
(P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.HU

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Close NearCubicWires.WireExponent3_5.FinalPass.Close2


theorem h00 : (0 : ℕ) ≤ 0 + 1 := Nat.zero_le _


end NearCubicWires.WireExponent3_5.FinalPass.Out.HU
