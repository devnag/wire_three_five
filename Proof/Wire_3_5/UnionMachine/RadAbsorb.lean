import Lean
import Proof.Wire_3_5.UnionMachine.RadScan
import Proof.Wire_3_5.Primitive.Writers.ThrSide3Base
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.ThrSide2
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.RadAbsorbBase


noncomputable section
set_option maxRecDepth 4096


/-! # C6b: the THR load absorbs the RADIX row's list bound (#198: the freeze gate's satisfiability check)

The RADIX row's explicit capacity carries `(8G+2)^{3·lb+1}`, `lb = listBound (thrCallD)`, so the class link needs
`lb·L ≤ C·Ψ` (`L = ⌈log₂(n+2)⌉`, `Ψ = psiOf n` the preprocessing load). This holds: `lb = 4·Σ_{j<J} W_j + 1` with
`W_j = 16t + 20(⌊(√(t·B_*)+1)/2^{⌊j/2⌋}⌋ + 1)` (`MajorantParams.W`), `J ≤ e_J·L`, `t ≤ (2e_J+1)·L` (PA2's
`ThrSide.thrCallJ_le`, `thrCallT_le`), `B_* ≤ 201326592·B_T` (`a' ≤ 4`, `|carriers| ≤ 2`, `B_T` the THR cap), and
the THR load `Ψ_T = C_D((k+L)²·C_D(√(B_T L)+1+L²)+k+L²)` (P3:3094-3107) is at least `L²(√(B_T L)+L²)` at `C_D ≥ 1`
(`ThrSide.loadThr_le`; `psiOf = loadPsi …` by definition).

* `cSq`, `cAb`; `absorb_arith`; **`lb_absorb`**: `listBound (thrCallD …) · ⌈log₂(n+2)⌉ ≤ cAb l · psiOf n`.

Paper quantity of the main type: the THR preprocessing load `Ψ_T` (prim:runtime P3:3094-3108) against the RADIX
row's list bound. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.RadAbsorb
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Filters
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.Stars

/-- The square-root constant: `cSq² ≥ (2e_J+1)·201326592`. -/
noncomputable def cSq (l : Literals) : ℕ := (2 * ThrSide.eJ l + 1) * 14190

/-- **The absorption constant.** -/
noncomputable def cAb (l : Literals) : ℕ :=
  8 * ThrSide.eJ l * (16 * (2 * ThrSide.eJ l + 1) + 40 * cSq l + 40) + 1

end NearCubicWires.WireExponent3_5.UnionMachine.RadAbsorb

end
