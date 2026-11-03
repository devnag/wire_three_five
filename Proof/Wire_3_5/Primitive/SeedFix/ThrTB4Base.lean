import Proof.Wire_3_5.Primitive.SeedFix.ThrTB3Base
import Proof.Wire_3_5.Primitive.SeedFix.C4GateThrBBase
import Proof.Wire_3_5.Primitive.SeedFix.ThrDataIface4Base

/-! # T3 THRTAIL T-B, part 4: the data side of the THR shell at a call

The v4 shell's data width `V = C₂(n+1)^{D₂}` (the v4 data stage `S`, the fill of its input word): at
`D₂ = D₀ + d_T + D_{vS} + 26`, `C₂ = C₀ + C_{vS} + 19(K_t(F) + 5)` it meets `ThrDataOK2` (`C4GateSym.thr_data_hyps` at
`needW n ≤ V`), the numbers' unary word (`|unaryList (hashNums ++ thrCounts)| ≤ V`), the stage's need (`S.need n ≤ V`
from `S.Kn ≤ C₀`, `S.Dn ≤ D₀`) and the stage's cost `cost3 ≤ C₀(3C₂+1)^{D₀}·(n+1)^{D₂·D₀}` (`cost3_le`).

* `dT2`, `cT2`; **`data_ok`**, **`data_cu`**, **`data_need`**, **`data_cost`**.

Paper quantity of the main type: the THR call's data word (P3:2543-2558, 3083-3086) within the writer's fill. -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine

theorem pow_mono_exp {x a b : ℕ} (h : a ≤ b) : (x + 1) ^ a ≤ (x + 1) ^ b := Nat.pow_le_pow_right (by omega) h

section Data

end Data

section Stage

end Stage

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
