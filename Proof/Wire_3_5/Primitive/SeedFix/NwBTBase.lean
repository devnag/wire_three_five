import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ5Base
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecR2
import Proof.Wire_3_5.Primitive.SeedFix.TS4OBase
import Proof.Wire_3_5.Primitive.Writers.SymDecNums
import Proof.Wire_3_5.UnionMachine.NumsPh3Base

/-! # T3 NW phase (b), the types: the value (b) computes, its link, its capacity atoms, its dock cost

Phase (b) (the `NumsPh3.PhB`) computes, at a THR call on the star, from W6's numbers `|𝒢|`, `cut`, `Σp`,
`#primes` (ports 3, 5, 7, 6), the gap numbers' `2^{sb}` and the star numbers' `n`, `k_h = s·⌊r/2⌋`:

* **`vVal`**: `V = 2^e·B·2^{sb}·#primes` with `q = 2|𝒢|·cut + 1`, `B = (|𝒢|·Σp·2^{sb}·q² + 1)·8192·n²`,
  `e = ⌊(5k_h + 3)/4⌋` (the THR sample count `Q = 2^e·B`, `ThrCap.thrQ_link`);
* **`vB`**: `vVal` at the call's numbers (`valsB` = W6's `thrNumVals` at `cap_T = capTL`, `|carriers|`; `gapB` =
  the gap parameters at `(2(n+1)^{26}, cap_T, f_e·L)`; `khB`);
* **`VLinkB l`**: at every THR call on the star, `vB = vOf` (P3:3044-3048: `|PrimeIndex(cut)|·|E|·Q`);
* **`AtomsB c Tf`** and **`NeedB l`**: every number (b)'s register programs hold is at most
  `K_n(F)·(|fpIn|+1)^{D_n(f_e)}` (the v4 need, `cap_T`, `(n+1)^{26}`, W6's power, W6's 14 numbers, the gap numbers,
  `V`, `T_f`; and `#primes ≥ 1`);
* **`CostB l`**: the two docked machines' cost at `V_d = tV(|fpIn|, n, cap_T)` is at most
  `K_c(F)·(|fpIn|+1)^{D_c(f_e)}`.

The phase-(b) term takes `VLinkB l`, `NeedB l`, `CostB l` as arguments.

Paper quantity of the main types: the final pass's unshifted denominator `V = |PrimeIndex(cut)|·|E|·Q` at a THR request
(P3:3044-3048) and its polynomial size in the input (P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimT.NwB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline

/-- **The value** `V = 2^e·B·2^{sb}·#primes`, `e = ⌊(5k_h+3)/4⌋`, `B = (|𝒢|·Σp·2^{sb}·q²+1)·8192·n²`,
`q = 2|𝒢|·cut + 1`. -/
def vVal (g c ps sb np n kh : ℕ) : ℕ :=
  2 ^ ((kh * 5 + 3) / 4) * ((g * ps * sb * (2 * (g * c) + 1) * (2 * (g * c) + 1) + 1) * 8192 * n * n) * sb * np

section Call

end Call

section Props

end Props

end NearCubicWires.WireExponent3_5.PrimT.NwB
