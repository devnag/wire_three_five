import Proof.Wire_3_5.FinalPass.Core14

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
variable {l : Literals} (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : S5Lay Sw0.nw)

/-- **The front's exit bank** at a request. -/
noncomputable def exitA (r : FReq l F kclk coef A a ha) (y : Fin L.t) : List Bool := by
  classical
  exact if h : ∃ k, L.wd k = y then frontWordsW2 l F kclk coef A a ha Sw0 r (Classical.choose h)
    else if y = L.tN then frame (binary (Sd.R.Tf l F kclk coef A a ha r) 0)
    else if y = L.tD then frame (binary (Sd.R.Tf l F kclk coef A a ha r) (fpDen l F kclk coef A a ha r))
    else List.replicate (blOf2 L r y) false

theorem exitA_wd (r : FReq l F kclk coef A a ha) (k : Fin (17 + Sw0.nw)) :
    exitA F kclk coef A a ha L r (L.wd k) = frontWordsW2 l F kclk coef A a ha Sw0 r k := by
  classical
  have h : ∃ k', L.wd k' = L.wd k := ⟨k, rfl⟩
  unfold exitA
  rw [dif_pos h]
  congr 1
  exact L.wdInj (Classical.choose_spec h)

theorem exitA_tN (r : FReq l F kclk coef A a ha) :
    exitA F kclk coef A a ha L r L.tN = frame (binary (Sd.R.Tf l F kclk coef A a ha r) 0) := by
  classical
  unfold exitA
  rw [dif_neg (fun ⟨k, hk⟩ => L.wdN k hk), if_pos rfl]

theorem exitA_tD (r : FReq l F kclk coef A a ha) :
    exitA F kclk coef A a ha L r L.tD =
      frame (binary (Sd.R.Tf l F kclk coef A a ha r) (fpDen l F kclk coef A a ha r)) := by
  classical
  unfold exitA
  rw [dif_neg (fun ⟨k, hk⟩ => L.wdD k hk), if_neg (Ne.symm L.hND), if_pos rfl]

theorem exitA_blank (r : FReq l F kclk coef A a ha) (y : Fin L.t) (hw : ∀ k, y ≠ L.wd k) (hN : y ≠ L.tN)
    (hD : y ≠ L.tD) : exitA F kclk coef A a ha L r y = List.replicate (blOf2 L r y) false := by
  classical
  unfold exitA
  rw [dif_neg (fun ⟨k, hk⟩ => hw k hk.symm), if_neg hN, if_neg hD]

end Exit

section Final
variable {l : Literals} (W : CoreWriters l) {mTh : ℕ} (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOf W))

/-- The final pad's cost. -/
def finCost (m c : ℕ) : ℕ := m * (6 * c + 17) + 1 + (6 * c + 10)

end Final

end NearCubicWires.WireExponent3_5.FinalPass.Core
