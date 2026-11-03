import Proof.Wire_3_5.Primitive.Writers.WriterIfaceJBase

/-! # PA (e): the writers' class link (the TYPE C6 proves), and the load-constant floor it needs

P3:3108, 3112-3114 (prim:runtime): the additive preprocessing of a call costs `2^{O(Ψ)}q^{O(1)}`, the class
`classBound E .preprocessing q k Ψ = 2^{cpsi·Ψ}·q^{Apre}`; P3:3094-3102: the load is
`Ψ = max{Ψ_T, Ψ_S, Ψ_aux}`, every term a multiple of the load constant `C_D` (`loadPsi`). The batch writers (SYM, THR,
HASH) run over the star cells, `2^{k+L}·poly(n)` units (`k = kOf n`, `L = ⌈log₂(n+2)⌉`; PA's `NumsX.mOf`).

* **`PreLink`** (the (e) TYPE, for C6): after the endpoint exponent `fe` and the writers' fixed polynomial
  `(D, C)`, a floor envelope `E_W` and a load-constant floor `CD_W`; for every admissible `F` above both floors, a
  coefficient `c_W` with `C·(2^{k+L} + n + 1)^D ≤ c_W · classBound E_W .preprocessing n k Ψ` at every call length.
* **`psiOf_eq_zero`**: at `F.CD = 0` the load `Ψ` is `0`, so **`preClass_zero`**: the
  preprocessing class is the polynomial `n^{Apre}`, which no writer over `2^{k}` cells meets (`k ≥ L`, and
  `k = r·⌊log₂(n/r+1)⌋` with `r = Θ(log L)` is superlogarithmic). `WriterIfaceJ.WriterLeafJ` has no `C_D` floor
  (SeedFixLeaf and FinalPassLeaf have one: `CD₄ ≤ F.CD`, `CD₅ ≤ F.CD`).
* **`WriterLeafJ2`**: the writers' target with the floor `CD_W ≤ F.CD`, in SeedFixLeaf's order of choice
  (`fe`, then `E_W` and `CD_W`, then `F`, then `c_W`).

Paper quantities of the main types: the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114) at the load `Ψ`
(P3:3094-3102) and the star cells' count `2^{k+L}`. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.PreLink
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIfaceJ

/-! ## The finding: without a floor on `C_D` the preprocessing class is polynomial -/

/-! ## The (e) TYPE -/

/-! ## The writers' target with the floor -/

end NearCubicWires.WireExponent3_5.PrimAsm.PreLink
