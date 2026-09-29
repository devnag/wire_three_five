import Proof.Wire_3_5.Primitive.Writers.BudgetIface2
import Proof.Wire_3_5.Primitive.Writers.PopSetupIface
import Proof.Wire_3_5.Primitive.Writers.WritersJoin

/-! # The SYM writer's leaf from its producers (type)

The SYM writer's deliverable is `WritersJoin.SymLeafJ2 l`. Its machine is the SYM shell v2 at `m_S`
(`ShellS.shell_runSym`) with PA's SYM unit decode (`SymDec.decW`, the FILTER bank and the POP bank `pbW`); the tape is
`SymDec.sym_loop_tape`. Its budget needs, besides PA's own machines, these producers:

* the walk bank `W`, the FILTER setup `FS : FiltSetupSpec5 W` (`fsSpec`), the POP setup
  `Q : PopSetupSpecB W` (after this leaf; its need and bound explicit);
* `BudgetIface2.FiltPipeLe2` (verified: the SYM FILTER units' pipeline);
* **`PopPipeLe`**: the POP units' pipeline cost `PopPipe.popPipeBound` at the setup's explicit parameters
  (`popMlab`, `popLw`, `popR`, `popCp`, `popRW`) is at most `K_p·(cap + M + B + e + L + r4 + G + off + |FlatSeed| +
  (8L+2)^{3·lbP+1} + 2)^{D_p}·2^{D_p·e}`: polynomial in the capacity, the list's numbers, the slice and the POP row's
  counting capacity `(8L+2)^{3·lbP+1}` (`PopSetupSpecB.need_le`'s measure), times the walk's `2^{O(e)}`
  (`popRow_run`: `2^t·128·(|record|+1)³`, `t = 2⌊e/4⌋+1`).

**`SymLeafOf l`**: from these, the SYM writer's leaf. The construction proves it (the class link at `m_S = mOfT K_F P + T`,
`T = O(D₂·Z·L²·√B_S)` against `Ψ_S ≥ C_D²(k+L)²√B_S`, as `HashFam`/`HashClass` for the HASH writer).

Paper quantities of the main types: the POP row's cost (list:flatten P3:1491-1498, row:sym P3:2477-2496) and the SYM
tape `symTape` within the preprocessing class `2^{O(Ψ)}q^{O(1)}` (P3:3108, 3112-3114). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Lists NearCubicWires.WireExponent3_5.PrimAsm.PopSetup
open NearCubicWires.WireExponent3_5.PrimAsm.PopLink NearCubicWires.WireExponent3_5.PrimAsm.Emit

/-- **The POP pipeline's cost bound** (at the POP setup's explicit parameters). -/
def PopPipeLe : Prop :=
  ∃ Kp Dp : ℕ, ∀ (cap : ℕ) (Pl : FlatListParams) (e : Pl.FlatSeed) (L r4 G off : ℕ) (sgn : Bool) (s : Fin (Pl.M + 1))
    (hlabs : 4 * L ≤ (sliceLabs r4 G off L).length),
    PopPipe.popPipeBound cap Pl e L r4 G off (popMlab r4 G off L) (popLw Pl L) (popR Pl r4 G off L)
        (popCp Pl r4 G off L) (popRW Pl) (popRW Pl) sgn s hlabs ≤
      Kp * (cap + Pl.M + Pl.B + Pl.errExp + L + r4 + G + off + Fintype.card Pl.FlatSeed +
        (8 * L + 2) ^ (3 * lbP Pl + 1) + 2) ^ Dp * 2 ^ (Dp * Pl.errExp)

end NearCubicWires.WireExponent3_5.PrimAsm.SymLeaf
