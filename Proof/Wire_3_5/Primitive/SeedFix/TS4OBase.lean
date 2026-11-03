import Proof.Wire_3_5.Primitive.Writers.CallIndexRBase
import Proof.Wire_3_5.Primitive.Writers.SymNeedBase
import Proof.Wire_3_5.Primitive.SeedFix.TS4V

/-! # T (#120, thrStage4U), part 13: the capacity need is polynomial

P3:3114-3115 ("All powers of `n` are fixed before a fixed `r`"): `needT l c_r n ≤ NCoef l c_r·(n+1)^{NDeg l}`, the degree
`NDeg l` fixed by the literals (the cap's exponents, W6's `Eth`, the sparse bound's `spA`), the coefficient by `c_r`:

* `two_pow_le` (`(n+2)^d ≤ 2^d (n+1)^d`), `spT_le`, `capNT_le`, `needW_le`;
* `NDeg`, `NCoef`, **`needT_le`**.

Paper quantities of the main type: the v4 stage's capacity need (the THR cap, the sparse count, W6's need). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.Transfer NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

theorem two_pow_le (n d : ℕ) : (n + 2) ^ d ≤ 2 ^ d * (n + 1) ^ d := by
  rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) d

end NearCubicWires.WireExponent3_5.PrimT.TS4
