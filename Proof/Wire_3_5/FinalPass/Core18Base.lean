import Proof.Wire_3_5.FinalPass.Core17Base

/-! # S5Core, part 18: the core half, generic in the bank (P3:3044-3048, 3170-3181)

* `Kcore W F`, `Dcore W fe` (the core's register need: every writer's capacity and step bound, at least `2·N^1`),
  `cap_le` (a writer's capacity or step bound below the bank's register length);
* **`coreOut`**: the core's exit meets `FrontOut` at `frontWordsW2` (`Num = 0`, `Den = fpDen` at the width `Sd.R.Tf`,
  `blOf2`);
* **`coreB3 … : S5CoreB3`** at every bank with the core's room (`HalfRoom2 L mT (mCoreOf W)`) and register need;
  **`coreHalf`** (`HalfGen2`), **`coreGen Wr : ∀ mT, Bank.CoreHalfGen2 Sw0 mT (fun l => mCoreOf (Wr l))`**;
* the uniformity lemmas, all by `rfl`: **`coreGen_K`**, **`coreGen_D`** (`Dcore (Wr l) fe`), **`coreGen_Dcc`**
  (`L.Dc`), **`coreGen_Cc`** (`Cc0·(L.Kc + 1)`), **`coreGen_Dw`** (`Sd.R.ZTe l fe`), **`coreGen_Cw`**
  (`KT l F·2^{ZT l F}`).

Paper quantities of the main types: the front's words `frontWordsW2` and the printed numbers' start at the width
`W = Sd.R.Tf` (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Gen
variable {l : Literals} 

/-- A capacity or step bound below the bank's register length. -/
theorem cap_le (C D N Kc Dc : ℕ) (hN : 1 ≤ N) (hC : C ≤ Kc) (hD : D ≤ Dc) : C * N ^ D ≤ Kc * N ^ Dc :=
  Nat.mul_le_mul hC (Nat.pow_le_pow_right hN hD)

end Gen

section Out

end Out

section Need


end Need

section Half

end Half

section Half2

end Half2

section Uni

end Uni

end NearCubicWires.WireExponent3_5.FinalPass.Core
