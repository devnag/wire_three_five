import Proof.Wire_3_5.Primitive.Writers.ThrSide4

/-! # PA2 c4 THR block, piece 6 part 5: the THR free numbers and the enumeration's side conditions (`hok`)

The THR twin of the SymFr3/SymCap3 at the THR call: the free numbers `freeVal2 (thrK2 c) (thrX …)` (`m =
max(8·|carriers| + 16·τ₀, 8)`: the carrier rows have one factor, the RADIX row `2τ₀`, BShape5's
`thr_rows_factors`), the requests' degree bound `thrDF c x = d_D(⌊√(B_T L)⌋ + L²)` (the paper's `d_T`,
P3:3094-3100); at a THR call `n_T ≤ 2^{TWd}`, `Q ≥ 1`, `Q' ≤ pr`, `1 ≤ h`, and the enumeration's hypotheses at every
child prefix (`EnumCap.enumOk_of`, the capacity `2^{⌊n/16⌋ + d_C L²}`) under the THR load floor.

* **`thrK2`**, **`thrDF`**; `hnT_thr`, `hQ_thr`, `hQp_thr`, **`thrQ_of`**, **`thrHok`**.

Paper quantities of the main types: the THR free numbers and the enumeration's hypotheses at a THR call. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.PrimT.C4Set
open NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.SupplierPipeline NearCubicWires.WireExponent3_5.Stars NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.PrimAsm.WriterIface
open NearCubicWires.WireExponent3_5.FinalPass.FreeGen
open NearCubicWires.WireExponent3_5.FinalPass.SymFr (SymC symKn cK pow_N_le one_le_L n2_le_L pow_mono_mul)

/-- **The THR constants**: `m = max(8·|carriers| + 16·τ₀, 8)` (the field `M` of `thrX` is the digit count `τ₀`). -/
def thrK2 (c : SymC) : FreeK2 := ⟨⟨c.dT, c.dC, c.dQ, c.dH, 8, 0, 0, 0, 0, 16, c.dP, c.dA, c.dR⟩, c.eH, c.eP, 8⟩

/-- **The THR requests' degree bound** `d_D(⌊√(B_T L)⌋ + L²)` (the paper's `d_T = C_D(√(B_T L) + L²)`). -/
def thrDF (c : SymC) (x : FreeIn) : ℕ := c.dD * (Nat.sqrt (x.capS * β x) + β x * β x)

section Gate

end Gate

end NearCubicWires.WireExponent3_5.PrimAsm.ThrSide
