import Lean
import Proof.Wire_3_5.FinalPass.Core17
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Core11
import Proof.Wire_3_5.FinalPass.Core15
import Proof.Wire_3_5.FinalPass.Core16
import Proof.Wire_3_5.FinalPass.Core8
import Proof.Wire_3_5.FinalPass.CoreIfaceM
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR12
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsHalves
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5Seam2
import Proof.Wire_3_5.Primitive.Writers.S5SeamB
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.Core18Base


noncomputable section
set_option maxRecDepth 4096


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
variable {l : Literals} (W : CoreWriters l) (F : GateFree l)

/-- **The core's register coefficient**: every writer's capacity and step coefficient, at least `2`. -/
def Kcore : ℕ :=
  max 2 (max (max (W.SA.Kc F) (W.SA.Cs F)) (max (max (W.SB.Kc F) (W.SB.Cs F))
    (max (max (W.NW.Kc F) (W.NW.Cs F)) (max (W.SW.Kc F) (W.SW.Cs F)))))

end Gen

section Out
variable {l : Literals} (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (L : S5Lay Sw0.nw)

/-- **The core's exit meets `FrontOut`.** -/
theorem coreOut : FrontOut l F kclk coef A a ha L.wd ![L.tN, L.tD] (frontWordsW2 l F kclk coef A a ha Sw0)
    (fun r => ![0, fpDen l F kclk coef A a ha r]) (Sd.R.Tf l F kclk coef A a ha) (fun r j => blOf2 L r j)
    (fun _ _ => 0) (exitA F kclk coef A a ha L) where
  inj := fun k i => by
    fin_cases i
    · exact L.wdN k
    · exact L.wdD k
  wdInj := L.wdInj
  nmInj := outN_inj L
  heads := fun _ => rfl
  words := fun r k => exitA_wd F kclk coef A a ha L r k
  nums := fun r i => by
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]; exact exitA_tN F kclk coef A a ha L r
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]; exact exitA_tD F kclk coef A a ha L r
  numW := fun r i => by
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero]; exact Nat.one_le_two_pow
    · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.head_cons]; exact Sd.R.fpDen_ltR l F kclk coef A a ha r
  blank := fun r j hw hn => exitA_blank F kclk coef A a ha L r j (fun k => hw k) (hn 0) (hn 1)

end Out

section Need
variable {l : Literals} (W : CoreWriters l) (F : GateFree l) (fe : ℕ)

theorem k2 : 2 ≤ Kcore W F := by unfold Kcore; omega

end Need

section Half
variable {l : Literals} (W : CoreWriters l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
  (L : S5Lay Sw0.nw) {mTh : ℕ} (hR : Bank.HalfRoom2 L mTh (mCoreOf W))

/-- The width within `KT·2^{ZT}·(|fpIn|+1)^{ZT}`. -/
theorem core_W_le (r : FReq l F kclk coef A a ha) :
    Sd.R.Tf l F kclk coef A a ha r ≤
      Sd.R.KT l F * 2 ^ Sd.R.ZT l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Sd.R.ZTe l F.filterErrDeg := by
  have hn := FpInLen.n_le_fpIn r
  unfold Sd.R.Tf
  rw [← Sd.R.ZT_eq l F]
  have h2 : r.1.n + 2 ≤ 2 * ((fpIn l F kclk coef A a ha r).length + 1) := by omega
  calc Sd.R.KT l F * (r.1.n + 2) ^ Sd.R.ZT l F
      ≤ Sd.R.KT l F * (2 * ((fpIn l F kclk coef A a ha r).length + 1)) ^ Sd.R.ZT l F :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 _)
    _ = Sd.R.KT l F * 2 ^ Sd.R.ZT l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Sd.R.ZT l F := by
        rw [mul_pow]; ring

end Half

section Half2

end Half2

section Uni

end Uni

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
