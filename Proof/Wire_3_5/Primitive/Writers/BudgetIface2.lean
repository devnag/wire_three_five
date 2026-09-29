import Proof.Wire_3_5.UnionMachine.FiltSetupIface5

/-! # correction: the FILTER pipeline's cost bound with the exponent on the slice only

`BudgetIface.FiltPipeLe` raises the whole parameter sum to `D_f·(e+1)`. The row offset `r4 = 4·row` and the pool size
`G` enter the FILTER pipeline only polynomially (the labels' sizes: `labsCost`, `labCost`, `labSum`), but a writer's
rows range over all `2^{2k_h}` star cells, so `(r4 + …)^{D_f(e+1)} = 2^{Θ(k·L²)}` exceeds every writer's dimension
`2^{O(k + L³)}` (`k` superlogarithmic). The exponential factor of the pipeline is the FILTER row's `(4L+1)^{filtDeg}·
2^{filtDeg}` (`filtCostC`) in the slice length `L` alone, `filtDeg (filterTable P e L) = 3·(128·walkLen) + 1`.

* **`FiltPipeLe2`** (proves it): `filtPipeBound … ≤ K_f·(len + cap + e + L + r4 + G + off + 2)^{D_f}·
  (L + 2)^{D_f·(e+1)}`. It implies `BudgetIface.FiltPipeLe`'s bound.

Paper quantity of the main type: the FILTER row's cost `(4L+1)^{filtDeg}` (the regular filter's walk, P3:2063-2101)
at the error exponent `e` (P3:2210-2211), polynomial in the labels. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Filters

/-- **The FILTER pipeline's cost bound, v2**: polynomial in every parameter, times `(L+2)^{D_f(e+1)}` in the
slice length `L` only, uniformly in the seed. -/
def FiltPipeLe2 : Prop :=
  ∃ Kf Df : ℕ, ∀ (P : GapParams) (e : GapSeed P) (L r4 G off : ℕ), 1 ≤ P.cap →
    FiltPipe.filtPipeBound P e L r4 G off (FiltSetup.rulerW P) (FiltSetup.rulerW P) ≤
      Kf * (P.len + P.cap + P.errExp + L + r4 + G + off + 2) ^ Df * (L + 2) ^ (Df * (P.errExp + 1))

end NearCubicWires.WireExponent3_5.PrimAsm.BudgetIface
