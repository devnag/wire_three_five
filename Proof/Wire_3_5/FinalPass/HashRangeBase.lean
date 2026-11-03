import Proof.Wire_3_5.FinalPass.HashSz1Base
import Proof.Wire_3_5.FinalPass.SymCap2Base
import Proof.Wire_3_5.FinalPass.ThrSz3
import Proof.Wire_3_5.Primitive.Writers.BShape1
import Proof.Wire_3_5.Primitive.SeedFix.C4HD
import Proof.Wire_3_5.FinalPass.HashPops
import Proof.Wire_3_5.FinalPass.HashFreeBase
import Proof.Wire_3_5.FinalPass.FreeGenH2
import Proof.Wire_3_5.FinalPass.SymFr3Base

/-! # The HASH call's recovery range (`HashEAt`'s range clause)

filt:aux-precision (P3:2291-2296): "`Q_aux > log₂Δ₀ + k + s_aux + log₂(H_max+1)`, `Q_aux = O_D(k + L³)`". At a THR call's
HASH stage with the HASH constants `hashK2 c` (`m = 2t + 1`, `Q' = d_Q(β³ + 2k_h + β)`), the printed objective at every
prefix of at most `2t·ℓ₀` bits is nonnegative and `2^{m−1}·V < 2^{Q'}` once `d_Q ≥ 8e_R + 1`: the value is at most
`N²·n_E·|pops|·2^{2tℓ₀}·Π_j W_j^{2t}·(M + J(3M)^{2t}) ≤ 2^{k + e_R X³ − 2t}` (`HashSz1`, `HashSz2`, `HashPops`).

* `hashK2`, `eR`, `m_hash`, `Q_hash`, `mj_le`, **`bnd_le`**, **`hrange_hash`**.

Paper quantities of the main types: the HASH recovery precision `Q'` against the printed column value. -/

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

/-- **The HASH constants** on the SYM record: `m = 2·a + 1` (the arity slot holds `t`), no floor. -/
def hashK2 (c : SymC) : FreeK2 := ⟨⟨c.dT, c.dC, c.dQ, c.dH, 0, 0, 0, 2, 1, 0, c.dP, c.dA, c.dR⟩, c.eH, c.eP, 0⟩

section Gate

end Gate

end NearCubicWires.WireExponent3_5.FinalPass.HashFr
