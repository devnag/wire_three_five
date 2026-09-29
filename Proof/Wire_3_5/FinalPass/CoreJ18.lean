import Proof.Wire_3_5.FinalPass.CoreJ17

/-! # S5Core over the writers with arbitrary residues, part J18: the core half, generic in the bank (P3:3044-3048, 3170-3181)

* `KcoreJ W F`, `DcoreJ W fe` (the core's register need: every writer's capacity and step bound, at least `2·N^1`),
  `cap_le` (a writer's capacity or step bound below the bank's register length);
* **`coreOut`**: the core's exit meets `FrontOut` at `frontWordsW2` (`Num = 0`, `Den = fpDen` at the width `Sd.R.Tf`,
  `blOf2`);
* **`coreB3J … : S5CoreB3`** at every bank with the core's room (`HalfRoom2 L mT (mCoreOfJ W)`) and register need;
  **`coreHalfJ`** (`HalfGen2`), **`coreGenJ Wr : ∀ mT, Bank.CoreHalfGen2 Sw0 mT (fun l => mCoreOfJ (Wr l))`**;
* the uniformity lemmas, all by `rfl`: **`coreGen_KJ`**, **`coreGen_DJ`** (`DcoreJ (Wr l) fe`), **`coreGen_DccJ`**
  (`L.Dc`), **`coreGen_CcJ`** (`Cc0J·(L.Kc + 1)`), **`coreGen_DwJ`** (`Sd.R.ZTe l fe`), **`coreGen_CwJ`**
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
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l)

/-- **The core's register coefficient**: every writer's capacity and step coefficient, at least `2`. -/
def KcoreJ : ℕ :=
  max 2 (max (max (W.SA.Kc F) (W.SA.Cs F)) (max (max (W.SB.Kc F) (W.SB.Cs F))
    (max (max (W.NW.Kc F) (W.NW.Cs F)) (max (W.SW.Kc F) (W.SW.Cs F)))))

/-- **The core's register degree** (on `fe`): every writer's capacity and step degree, at least `1`. -/
def DcoreJ (fe : ℕ) : ℕ :=
  max 1 (max (max (W.SA.Dk fe) (W.SA.Ds fe)) (max (max (W.SB.Dk fe) (W.SB.Ds fe))
    (max (max (W.NW.Dk fe) (W.NW.Ds fe)) (max (W.SW.Dk fe) (W.SW.Ds fe)))))

end Gen

section Out

end Out

section Need
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (fe : ℕ)

theorem kA1J : W.SA.Kc F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem kA2J : W.SA.Cs F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem kB1J : W.SB.Kc F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem kB2J : W.SB.Cs F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem kN1J : W.NW.Kc F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem kN2J : W.NW.Cs F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem kS1J : W.SW.Kc F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem kS2J : W.SW.Cs F ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem k2J : 2 ≤ KcoreJ W F := by unfold KcoreJ; omega
theorem dA1J : W.SA.Dk fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem dA2J : W.SA.Ds fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem dB1J : W.SB.Dk fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem dB2J : W.SB.Ds fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem dN1J : W.NW.Dk fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem dN2J : W.NW.Ds fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem dS1J : W.SW.Dk fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem dS2J : W.SW.Ds fe ≤ DcoreJ W fe := by unfold DcoreJ; omega
theorem d1J : 1 ≤ DcoreJ W fe := by unfold DcoreJ; omega

end Need

section Half
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
  (L : S5Lay Sw0.nw) {mTh : ℕ} (hR : Bank.HalfRoom2 L mTh (mCoreOfJ W))

/-- The core half's run at a bank with its register need. -/
theorem coreB3_runJ (hK : KcoreJ W F ≤ L.Kc) (hD : DcoreJ W F.filterErrDeg ≤ L.Dc) (r : FReq l F kclk coef A a ha) (Ab : Fin L.t → List Bool)
    (hE : ThrExit2 l F kclk coef A a ha Sw0 L r Ab) :
    Step (coreMJ W F L hR) (coreCostJ W F kclk coef A a ha L hR r) (fun _ => 0) Ab (fun _ => 0)
      (exitA F kclk coef A a ha L r) := by
  have hN : 1 ≤ (fpIn l F kclk coef A a ha r).length + 1 := by omega
  have hKc : 2 ≤ L.Kc := (k2J W F).trans hK
  have hDc : 1 ≤ L.Dc := (d1J W _).trans hD
  have hc2 : 2 * ((fpIn l F kclk coef A a ha r).length + 1) ≤
      L.Kc * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc :=
    Nat.mul_le_mul hKc ((Nat.pow_one _).symm.le.trans (Nat.pow_le_pow_right hN hDc))
  exact core_runJ W F kclk coef A a ha L hR r Ab hE hc2
    (cap_le _ _ _ _ _ hN ((kA1J W F).trans hK) ((dA1J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kA2J W F).trans hK) ((dA2J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kB1J W F).trans hK) ((dB1J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kB2J W F).trans hK) ((dB2J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kN1J W F).trans hK) ((dN1J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kN2J W F).trans hK) ((dN2J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kS1J W F).trans hK) ((dS1J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kS2J W F).trans hK) ((dS2J W _).trans hD))

/-- The core half's cost within `s5Bound`. -/
theorem coreB3_costJ (hK : KcoreJ W F ≤ L.Kc) (hD : DcoreJ W F.filterErrDeg ≤ L.Dc) (r : FReq l F kclk coef A a ha) :
    coreCostJ W F kclk coef A a ha L hR r ≤
      PrimAsm.S5Seam.s5Bound l F kclk coef A a ha (Cc0J W L * (L.Kc + 1)) L.Dc r := by
  have hN : 1 ≤ (fpIn l F kclk coef A a ha r).length + 1 := by omega
  have hDc : 1 ≤ L.Dc := (d1J W _).trans hD
  have h := coreCost_leJ W F kclk coef A a ha L hR r hDc
    (cap_le _ _ _ _ _ hN ((kA2J W F).trans hK) ((dA2J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kB2J W F).trans hK) ((dB2J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kN2J W F).trans hK) ((dN2J W _).trans hD))
    (cap_le _ _ _ _ _ hN ((kS2J W F).trans hK) ((dS2J W _).trans hD))
  refine h.trans ?_
  unfold PrimAsm.S5Seam.s5Bound
  have h1 : 1 ≤ 2 ^ (L.Dc * PrimAsm.S5Seam.s5Psi l F kclk coef A a ha r) := Nat.one_le_two_pow
  calc Cc0J W L * ((L.Kc + 1) * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc)
      = Cc0J W L * (L.Kc + 1) * 1 * ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc := by ring
    _ ≤ Cc0J W L * (L.Kc + 1) * 2 ^ (L.Dc * PrimAsm.S5Seam.s5Psi l F kclk coef A a ha r) *
        ((fpIn l F kclk coef A a ha r).length + 1) ^ L.Dc :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h1)

/-- **The core half at a bank** with its room and register need. -/
noncomputable def coreB3J (hK : KcoreJ W F ≤ L.Kc) (hD : DcoreJ W F.filterErrDeg ≤ L.Dc) :
    S5CoreB3 l F kclk coef A a ha Sw0 L where
  s := _
  M := coreMJ W F L hR
  cost := coreCostJ W F kclk coef A a ha L hR
  W := Sd.R.Tf l F kclk coef A a ha
  hW := Sd.R.ptv_lt l F kclk coef A a ha
  exitA := exitA F kclk coef A a ha L
  run := coreB3_runJ W F kclk coef A a ha L hR hK hD
  out := coreOut F kclk coef A a ha L
  Cc := Cc0J W L * (L.Kc + 1)
  Dcc := L.Dc
  cost_le := coreB3_costJ W F kclk coef A a ha L hR hK hD
  Cw := Sd.R.KT l F * 2 ^ Sd.R.ZT l F
  Dw := Sd.R.ZTe l F.filterErrDeg
  W_le := core_W_le F kclk coef A a ha

end Half

section Half2
variable {l : Literals} (W : CoreWritersJ l) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The core half, generic in the bank** (`HalfGen2`), at the THR room `mTh`. -/
noncomputable def coreHalfJ (mTh : ℕ) :
    Bank.HalfGen2 (fun L : S5Lay Sw0.nw => S5CoreB3 l F kclk coef A a ha Sw0 L) mTh (mCoreOfJ W) where
  K := KcoreJ W F
  D := DcoreJ W F.filterErrDeg
  half := fun L hR hK hD => coreB3J W F kclk coef A a ha L hR hK hD

end Half2

/-- **The core half's target** (`Bank.CoreHalfGen2`, the finish term's `core`) from its four writers, for every THR
room. -/
noncomputable def coreGenJ (Wr : ∀ l : Literals, CoreWritersJ l) (mT : Literals → ℕ) :
    Bank.CoreHalfGen2 Sw0 mT (fun l => mCoreOfJ (Wr l)) :=
  fun l F kclk coef A a ha => coreHalfJ (Wr l) F kclk coef A a ha (mT l)

section Uni

end Uni

end NearCubicWires.WireExponent3_5.FinalPass.Core
