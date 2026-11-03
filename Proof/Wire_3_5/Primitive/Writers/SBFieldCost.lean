import Lean
import Proof.Wire_3_5.Primitive.Writers.SBTypes2
import Statement_Wire_3_5
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Assembly.GateUnion
import Proof.Wire_3_5.Primitive.Writers.SBLay
import Proof.Wire_3_5.Primitive.Writers.SBTypes
import Proof.Wire_3_5.Recovery.RecoverySetup
import Proof.Wire_3_5.Primitive.Writers.SBFieldCostBase


noncomputable section
set_option maxRecDepth 4096


/-! # SB: the field phase's cost target, proved

* `zerosCost_eq`, `eraseListCost_eq`, `eraseL_length`, `two_pow_ell` (`2^ℓ ≤ 32·len`), `fieldCost_le` (within
  `10^7·cap^4` once `4ℓ + 6 ≤ cap` and `len ≤ cap`), **`sbFieldCost : SBFieldCostStmt l`**.

Donors: `GF2.searchCost_le` (the primitive search, `2^{O(ℓ)}`), `PrimT.tauCost_le` (`250·(ℓ+1)^4`).

Paper quantity of the main type: SB's budget (`prim:runtime`, P3:3105-3115), the field words' cost (P3:2053-2055). -/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.SBAsm
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.SBTypes NearCubicWires.WireExponent3_5.PrimAsm.WriteNat

/-- **The field phase's cost target, proved.** -/
theorem sbFieldCost (l : Literals) : SBFieldCostStmt l := by
  refine ⟨10 ^ 7, 4, fun F P m wl c0 c1 nc cap h => ?_⟩
  have hp := need_parts l F.cr F.filterErrDeg P m wl c0 c1 nc cap h
  have ht1 := hp.1
  have hl := hp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlen : (P.n + 1) ^ 26 * 2 ≤ cap := by
    refine le_trans ?_ ht1
    unfold tB1
    omega
  exact fieldCost_le P.n cap hl hlen

end NearCubicWires.WireExponent3_5.PrimAsm.SBAsm

end
