import Proof.Wire_3_5.Primitive.Writers.PopSetupIface

/-! # POP setup: the POP-setup machine with its bounds, the need measure with the row offset `r4`

`PopSetup.PopSetupSpecB` bounds the setup's need by the POP row's counting capacity and the row's values, but its
measure sees the row offset `r4` only through `popMlab = off + L + (r4+4)·G`: at `G = 0` it does not see `r4`, while
the POP-ready state's capacity condition `PopReady.hcap3` reads `r4` itself, so `PopSetupSpecB` has no inhabitant.

* **`PopSetupSpecB2 W`**: `PopSetupSpec W` plus `need_le` with the measure
  `(8L+2)^{3·lbP+1} + popMlab + r4 + M + B + errExp + |FlatSeed| + 2` and `bound_le` (the bound `Kb·(c+1)^{Db}`).

Paper quantity of the main type: the POP-ready unit state of the flat list's row at the call's list seed (list:flatten
P3:1491-1498), within the preprocessing class `2^{O(Ψ)}` (prim:runtime P3:3089-3108). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Lists
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimT.WalkBank

/-- **The POP-setup machine with its bounds** (the need's measure reads the row offset `r4`). -/
structure PopSetupSpecB2 (W : WalkBankProducer) extends PopSetupSpec W where
  /-- the need is polynomial in the POP row's counting capacity `(8L+2)^{3·lbP+1}` and the row's values -/
  Kn : ℕ
  Dn : ℕ
  need_le : ∀ (Pl : FlatListParams) (L r4 G off : ℕ), need Pl L r4 G off ≤
    Kn * ((8 * L + 2) ^ (3 * lbP Pl + 1) + popMlab r4 G off L + r4 + Pl.M + Pl.B + Pl.errExp +
      Fintype.card Pl.FlatSeed + 2) ^ Dn
  /-- the bound is polynomial in the capacity -/
  Kb : ℕ
  Db : ℕ
  bound_le : ∀ c : ℕ, bound c ≤ Kb * (c + 1) ^ Db

end NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
