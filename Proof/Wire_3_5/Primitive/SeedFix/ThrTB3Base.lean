import Proof.Wire_3_5.Primitive.SeedFix.ThrTB2
import Proof.Wire_3_5.Primitive.SeedFix.ThrDecQ7Base
import Proof.Wire_3_5.UnionMachine.ThrDimCBase

/-! # T3 THRTAIL T-B, part 3: the THR dimension at a call

T-A's stage `thrDimStageG l F K_L K_f` at the call's star parameters `P`: its dimension `m_T P` lies
between `k + L + K_L·L² + K_f·Ψ_T` and `k + L + K_L·L² + 8K_f·Ψ_T` (`m_ge`, `m_le`; `mOf P = 2k_h + L = k + L`,
`ψ_T(P) = Ψ_T` at the call's budget, P3:3094-3107). At `K_L = kLT l f_e D₀`, `K_f = D₀ + 1` the dimension covers the
unit's measure (`meas ≤ D₀·2^m`, THRU4's `meas_le`), the unit count (`thrTOT ≤ C_L·2^m`, `tot_eq` + the decode's
atom bounds) and the request (`|w| ≤ 2^m`, `ThrMeas.word_le`).

* `kLT`, `kFT`, `cLT`; **`dim_ge`**, **`dim_le`**, **`meas_le_dim`**, **`tot_le_dim`**, **`w_le_dim`**.

Paper quantity of the main type: the THR writer's dimension `2^{m_T}`, `m_T = Θ(Ψ_T)` (P3:3094-3107). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.ThrTB
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Cost
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.Primitive NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.UnionMachine

/-- The dimension's load multiplier (from `D₀`). -/
def kFT (D0 : ℕ) : ℕ := D0 + 1

section Call

end Call

section Cover

end Cover

end NearCubicWires.WireExponent3_5.PrimT.ThrTB
