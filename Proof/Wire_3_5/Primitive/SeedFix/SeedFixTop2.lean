import Proof.Wire_3_5.Primitive.SeedFix.SeedFixTop
import Proof.Wire_3_5.Primitive.Writers.PreLink

/-! # SEEDFIX: the enclosing term with the writers' load-constant floor

Paper: "There are `O_D(L²+k+L)` seed-prefix decisions, each with a constant number of exact printer calls. Under the
displayed allowances the printer applies, and the explicit descriptions and their construction give the middle term in
`prim:runtime`" (P3:3170-3173). The load `Ψ` of `prim:runtime` is a multiple of the load constant `C_D`
(P3:3094-3102), fixed large enough before `r` (P3:3114-3115, 3185-3190).

`SeedFixTop.seedFixLeaf_of` takes the writers without a floor on `C_D` (`WriterIfaceJ.WriterLeafJ`), which no writer
over the `2^k` star cells meets at `C_D = 0` (`PreLink.psiOf_eq_zero`, `PreLink.preClass_zero`). This file takes them
with the floor (`PreLink.WriterLeafJ2`, SeedFixLeaf's order of choice):

* **`seedFixLeaf_of2`**: `WriterLeafJ2 l → C4Leaf l → SeedFixLeaf l`, with the floors `envMax E_W E₄` and
  `max CD_W CD₄` and the coefficient `3c₄ + 2c_W + 6` (the same assembly `SeedFixTop.seedFixAt_of`).

Paper quantity of the main type: the fixed seeds `seedWord` (`SeedFixLeaf`, through `SeedFixAt`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.SeedFixTop2
open NearCubicWires NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.PreLink
open NearCubicWires.WireExponent3_5.PrimT.SeedFixTypes NearCubicWires.WireExponent3_5.PrimT.SeedFixTop

/-- **PA's residual `SeedFixLeaf` from the writers with the load-constant floor and the C4 part** (the seedfix
reduce's enclosing term): the floors are `envMax E_W E₄` and `max CD_W CD₄`, the coefficient
`3c₄ + 2c_W + 6`. -/
noncomputable def seedFixLeaf_of2 (l : Literals) (w : WriterLeafJ2 l) (c4 : C4Leaf l) : SeedFixLeaf l :=
  fun fe => ⟨envMax (w fe).1 (c4 fe).1, max (w fe).2.1 (c4 fe).2.1, fun F hF hE hCD =>
    ⟨3 * ((c4 fe).2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE)
          (le_trans (le_max_right _ _) hCD)).1 +
        2 * ((w fe).2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
          (le_trans (le_max_left _ _) hCD)).1 + 6,
      fun kclk coef A a ha => seedFixAt_of
        (((w fe).2.2 F hF (classLE_trans (classLE_envMax_left _ _) hE)
          (le_trans (le_max_left _ _) hCD)).2 kclk coef A a ha)
        (((c4 fe).2.2 F hF (classLE_trans (classLE_envMax_right _ _) hE)
          (le_trans (le_max_right _ _) hCD)).2 kclk coef A a ha)
        (envMax (w fe).1 (c4 fe).1) (classLE_envMax_left _ _) (classLE_envMax_right _ _)⟩⟩

end NearCubicWires.WireExponent3_5.PrimT.SeedFixTop2
