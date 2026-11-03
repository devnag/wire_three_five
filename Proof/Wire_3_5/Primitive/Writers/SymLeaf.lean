import Proof.Wire_3_5.Primitive.Writers.SymFamCostBase
import Proof.Wire_3_5.Primitive.Writers.HashLeafBase

/-! # SYM leaf, part 13: the SYM writer's leaf

**`symLeaf : SymLeafOf l`**: from the walk bank, the FILTER setup (`FiltSetupSpec5 W`), the POP setup
(`PopSetupSpecB W`), `FiltPipeLe2` and `PopPipeLe`, the SYM writer's leaf `WritersJoin.SymLeafJ2 l`. After `fe`: the
floor envelope `E_W = SymFam.SB.EW` (`c_ψ = E_tot·c_S`, the budget's exponent in `Q = 2^{m_S} + 1` times the class
link's `c_S = 196608·Z·26 + 29`, functions of the producers' and the literals' exponents only) and the floor `C_D ≥ 1`;
after `F`: the coefficient `c_W = SymFam.SB.cWr` (with the cap's `capK c_r`, `c_r`, `fe`, the dimension's `K_F`); at every
clock and source work, the machine `SymFam.symWM` (the SYM shell v2 with PA's SYM unit decode) and its run
(`sym_fam_run`) within `c_W·classBound` (`sym_fam_cost`).

* `ppK`, `ppD` (`PopPipeLe`), `sbF` (the base constants after `F`), `sbE` (the exponents, with the floors), `sbF_cpsi`;
* **`symLeaf`**.

Paper quantity of the main type: the SYM tape `symTape` (C4's `BAT` word of the call, P3:3011-3016) within the
preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.SymFam
open NearCubicWires.WireExponent3_5.PrimAsm.HashLeaf NearCubicWires.WireExponent3_5.Transfer
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-! ## The producers' constants -/

noncomputable def ppK (hpp : PopPipeLe) : ℕ := Classical.choose hpp
noncomputable def ppD (hpp : PopPipeLe) : ℕ := Classical.choose (Classical.choose_spec hpp)
theorem pp_spec (hpp : PopPipeLe) : ∀ (cap : ℕ) (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool)
    (s : Fin (Pl.M + 1)) (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length),
    PopPipe.popPipeBound cap Pl e L r4 G off (popMlab r4 G off L) (popLw Pl L) (popR Pl r4 G off L)
        (popCp Pl r4 G off L) (popRW Pl) (popRW Pl) sgn s hlabs ≤
      ppK hpp * (cap + Pl.M + Pl.B + Pl.errExp + L + r4 + G + off + Fintype.card Pl.FlatSeed +
        (8 * L + 2) ^ (3 * lbP Pl + 1) + 2) ^ ppD hpp * 2 ^ (ppD hpp * Pl.errExp) :=
  Classical.choose_spec (Classical.choose_spec hpp)

/-! ## The leaf -/

end NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf
