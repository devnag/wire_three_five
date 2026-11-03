import Proof.Wire_3_5.FinalPass.HashPre1Base
import Proof.Wire_3_5.FinalPass.SymCost5Base

/-! # The HASH stage's pad and its request's numbers (`HashEAt`'s `hR`, `Q' ≤ pr`, `1 ≤ h`)

P3:3098-3100 (the pad `2^ρ`, `ρ = max(n − 2k_h + d_Aβ, d_Rβ²)`) at a THR call's HASH stage: the HASH child family's
loop cell (cost `2K_ch + 2`, `K_ch = symKch = 2^{n − k + d_A L − 4}`, the comparison at the sum's width
`W = Q' + 2dRow + 2(pr+1) + 4` and the `s_h = 2t·ℓ₀` decisions, P3:2238-2251) fits the pad: the cell is
`4K_ch + 146W + 10s_h + 79`, `4K_ch = 2^{n−k+d_A L−2}`, and `146W + 10s_h + 79 ≤ c_Pad(n+1)^{e_P+3} ≤ 2^{n−k+d_A L−2}`
once `d_A ≥ e_P + 5 + ⌈log₂ c_Pad⌉` (fixed before `F`). Also `Q' ≤ pr` (from `h·Q'·d ≤ pr`) and `1 ≤ h`.

* `cPad`, **`padHR_hash`**, `hQp_hash`, `one_le_h_hash`.

Paper quantities of the main types: the HASH loop cell's steps against the pad `2^ρ`; the request's `Q' ≤ pr`. -/

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

section Gate
variable (l : Literals) 

/-- **`1 ≤ h`** at the HASH request. -/
theorem one_le_h_hash (c : SymC) (hdH : 1 ≤ c.dH) (x : FreeIn) : 1 ≤ (FreeGen.freeProgH (hashK2 c)).val x 3 := by
  show 1 ≤ c.dH * (x.n + 1) ^ c.eH
  exact Nat.mul_le_mul hdH (Nat.one_le_pow _ _ (by omega))

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
