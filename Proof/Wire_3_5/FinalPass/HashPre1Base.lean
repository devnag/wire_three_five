import Proof.Wire_3_5.FinalPass.HashRangeBase
import Proof.Wire_3_5.FinalPass.HashRows
import Proof.Wire_3_5.FinalPass.SymPool

/-! # The HASH child request's precondition, part 1: the request's numbers at a THR call

alg:compiler (P3:1882-1900) at the HASH child request `hR R0 D p'` (the call's THR pool request `thrR0 … h Q' 0 m d pr 0`
with the printed HASH objective): with the HASH constants `hashK2 c` and the degree bound `d = d_D·β²`
(`hashDF`, the aux FILTER rows' degree `384·w_aux + 1 = O(L²)`, filt:soft P3:2253-2290), under the constraints
`HpreH`: the aux rows' degree is within `d`, the printed expression has at most `2^{k + c_V X²}` terms, `h·Q'·d ≤ pr`
and `|c|·2^{Q'} ≤ 2^{pr}` (the cleared weights `≤ Π_j W_j^{2t}·2^{2tℓ₀}`).

* `hashDF`, `cV`, `HpreH`; `walk_le`, **`lenV_le`**, **`hqd_hash`**, **`coef_hash`**.

Paper quantities of the main types: the HASH child request's `A`, `d`, `h·Q'·d` and coefficient widths. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace NearCubicWires.WireExponent3_5.FinalPass.HashFr
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.SymFr
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen

/-- **The HASH requests' degree bound** `d = d_D·β²` (the aux FILTER rows' degree is `O(L²)`). -/
def hashDF (c : SymC) (x : FreeIn) : ℕ := c.dD * (β x * β x)

theorem L_le_n (n : ℕ) : Nat.clog 2 (n + 2) ≤ n + 1 :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n + 1))

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
