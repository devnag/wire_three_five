import Proof.Wire_3_5.Primitive.Writers.S5Seam2

/-! # The S5 halves over the SYM words, with their cost bounds

The twin of `S5SeamB` over `S5Seam2`: the halves' targets with the preprocessing-class bound `s5Bound`
(`C·2^{D·ψ}·(|fpIn|+1)^D`, unchanged from `S5SeamB`).

* **`S5ThrB2`** (the target), **`S5CoreB2`** (the target), **`s5_cost_le2`** (the two halves in sequence within
  `s5Bound (Ct + Cc + 1) (max Dt Dcc)`).

Paper quantity of the main types: the front's running time inside the call's additive preprocessing term `2^{O(Ψ)}`
(prim:runtime, P3:3105-3115). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.BlockPlatform NearCubicWires.ExtDecompositionBatch

section Family
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (Sw : SymWords)

/-- **The THR half with its cost bound** (the target): `s5Bound`'s preprocessing form. -/
structure S5ThrB2 (L : S5Lay Sw.nw) extends S5Thr2 l F kclk coef A a ha Sw L where
  Ct : ℕ
  Dt : ℕ
  cost_le : ∀ r, cost r ≤ s5Bound l F kclk coef A a ha Ct Dt r

end Family

end NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
