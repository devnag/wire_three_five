import Proof.Wire_3_5.FinalPass.Core13Base

/-! # S5Core, part 15: the core half's exit (P3:3044-3048, 3170-3181)

* **`exitA L r`**: the front's exit bank (`FrontOut` at `frontWordsW2`): the words on their tapes, `Num = 0` and
  `Den = fpDen` in `Tf`-bit binary on `tN`, `tD`, every other tape `0^{blOf2}`; `exitA_wd`, `exitA_tN`, `exitA_tD`,
  `exitA_blank`;
* **`stageF`**: the final pad (every register tape off the words and the numbers padded against `Tc`, then `Tc`
  erased).

Paper quantities: the front's words and the printed numbers' start (P3:3044-3048, 3170-3181). -/

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
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length)
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)

section Exit

end Exit

section Final
variable {l : Literals} {mTh : ℕ} (L : S5Lay Sw0.nw) 

/-- The final pad's cost. -/
def finCost (m c : ℕ) : ℕ := m * (6 * c + 17) + 1 + (6 * c + 10)

end Final

end NearCubicWires.WireExponent3_5.FinalPass.Core
