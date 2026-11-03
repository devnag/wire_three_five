import Lean
import Proof.Wire_3_5.FinalPass.CoreJ16
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Core9
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.CoreJ11
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.CoreJ10


noncomputable section
set_option maxRecDepth 4096


/-! # S5Core over the writers with arbitrary residues, part J17: the core half's cost below one power (P3:3170-3181)

With the master bound `Y = (L.Kc + 1)·N^{L.Dc}` (`N = |fpIn| + 1`, `L.Dc ≥ 1`), which covers the register length
`c = L.Kc·N^{L.Dc}`, `N` and every writer's step bound: the count's chain (**`zCost_le`**), the count (`cnt_le`), the
mode (`mode_le`), each writer's stage (`stage_le`), the final pad (`fin_le`), and **`coreCost_leJ`**:
`coreCostJ ≤ Cc0J·Y`, `Cc0J = 200 + 80·Dc + 30·(nr_A + nr_B + nr_N + nr_S + L.t)`.

Paper quantity: the front's running time as a power of the input's length (P3:3170-3181). -/

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
open NearCubicWires.WireExponent3_5.FinalPass.S5T (mulCost)

section Cost
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {mTh : ℕ}
  (L : S5Lay Sw0.nw) (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- The cost's coefficient over the master bound. -/
def Cc0J : ℕ := 200 + 80 * L.Dc + 30 * (W.SA.nr + W.SB.nr + W.NW.nr + W.SW.nr + L.t)

/-- **The core half's cost below `Cc0J·(L.Kc + 1)·N^{L.Dc}`.** -/
theorem coreCost_leJ (r : FReq l F kclk coef A a ha) (hDc : 1 ≤ L.Dc)
    (hSA : W.SA.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SA.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hSB : W.SB.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SB.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hSN : W.NW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.NW.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
    (hSS : W.SW.Cs F * ((fpIn l F kclk coef A a ha r).length + 1) ^ W.SW.Ds F.filterErrDeg ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) :
    coreCostJ W F kclk coef A a ha L hR r ≤
      Cc0J W L * ((L.Kc + 1) * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc) := by
  have hLb : 2 * natBitLength r.1.n + 2 ≤ (fpIn l F kclk coef A a ha r).length := fpIn_len l F kclk coef A a ha r
  have hreg := regList_length L (TcJ W L hR)
  have hz := zCost_le ((fpIn l F kclk coef A a ha r).length + 1) L.Kc L.Dc (by omega) L.Dc le_rfl
  unfold coreCostJ cntCost modeCost finCost Cc0J
  generalize (fpIn l F kclk coef A a ha r).length = m at hLb hz hSA hSB hSN hSS ⊢
  have hP1 : 1 ≤ (m + 1) ^ L.Dc := Nat.one_le_pow _ _ (by omega)
  have hPN : m + 1 ≤ (m + 1) ^ L.Dc := Nat.le_self_pow (by omega) _
  have hcY : L.Kc * (m + 1) ^ L.Dc ≤ (L.Kc + 1) * (m + 1) ^ L.Dc := Nat.mul_le_mul_right _ (by omega)
  have hNY : m + 1 ≤ (L.Kc + 1) * (m + 1) ^ L.Dc := hPN.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hKY : L.Kc ≤ (L.Kc + 1) * (m + 1) ^ L.Dc := (Nat.le_succ _).trans (Nat.le_mul_of_pos_right _ hP1)
  generalize hYd : (L.Kc + 1) * (m + 1) ^ L.Dc = Y at hcY hNY hKY ⊢
  generalize hcd : L.Kc * (m + 1) ^ L.Dc = c at hcY hz hSA hSB hSN hSS ⊢
  have hY1 : 1 ≤ Y := by omega
  have pA := mul_share W.SA.nr c Y hcY hY1
  have pB := mul_share W.SB.nr c Y hcY hY1
  have pN := mul_share W.NW.nr c Y hcY hY1
  have pS := mul_share W.SW.nr c Y hcY hY1
  have pF := mul_share (regList L (TcJ W L hR)).length c Y hcY hY1
  have pT : (regList L (TcJ W L hR)).length * Y ≤ L.t * Y := Nat.mul_le_mul_right _ hreg
  have hD1 : L.Dc * c ≤ L.Dc * Y := Nat.mul_le_mul_left _ hcY
  have hD2 : L.Dc ≤ L.Dc * Y := Nat.le_mul_of_pos_right _ hY1
  have ez : L.Dc * (40 * c + 40) = 40 * (L.Dc * c) + 40 * L.Dc := by ring
  have e : (200 + 80 * L.Dc + 30 * (W.SA.nr + W.SB.nr + W.NW.nr + W.SW.nr + L.t)) * Y =
      200 * Y + 80 * (L.Dc * Y) + 30 * (W.SA.nr * Y) + 30 * (W.SB.nr * Y) + 30 * (W.NW.nr * Y) +
        30 * (W.SW.nr * Y) + 30 * (L.t * Y) := by ring
  rw [e]
  rw [ez] at hz
  generalize W.SA.nr * (6 * c + 17) = qA at pA ⊢
  generalize W.SB.nr * (6 * c + 17) = qB at pB ⊢
  generalize W.NW.nr * (6 * c + 17) = qN at pN ⊢
  generalize W.SW.nr * (6 * c + 17) = qS at pS ⊢
  generalize (regList L (TcJ W L hR)).length * (6 * c + 17) = qF at pF ⊢
  generalize W.SA.Cs F * (m + 1) ^ W.SA.Ds F.filterErrDeg = sA at hSA ⊢
  generalize W.SB.Cs F * (m + 1) ^ W.SB.Ds F.filterErrDeg = sB at hSB ⊢
  generalize W.NW.Cs F * (m + 1) ^ W.NW.Ds F.filterErrDeg = sN at hSN ⊢
  generalize W.SW.Cs F * (m + 1) ^ W.SW.Ds F.filterErrDeg = sS at hSS ⊢
  generalize zCost (m + 1) L.Kc L.Dc = z at hz ⊢
  omega

end Cost

end NearCubicWires.WireExponent3_5.FinalPass.Core

end
