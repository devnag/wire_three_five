import Lean
import Proof.Wire_3_5.FinalPass.Close4
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.Asm1
import Proof.Wire_3_5.FinalPass.Asm2
import Proof.Wire_3_5.FinalPass.AssemblyDock3
import Proof.Wire_3_5.FinalPass.Close2
import Proof.Wire_3_5.FinalPass.CoreJ11
import Proof.Wire_3_5.FinalPass.CoreJ18
import Proof.Wire_3_5.FinalPass.S5TInst
import Proof.Wire_3_5.FinalPass.S5TNum3
import Proof.Wire_3_5.FinalPass.S6Iface
import Proof.Wire_3_5.FinalPass.SdR12
import Proof.Wire_3_5.FinalPass.SeamsOut2
import Proof.Wire_3_5.FinalPass.Stage1
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.UnionMachine.SymSize2
import Proof.Wire_3_5.Foundations.OutMachineHUBase


noncomputable section
set_option maxRecDepth 120000


/-! # The uniformity bundle `hU`: S6's constants at the final pass's parts

"The coefficients depend only on the gate, the degrees only on the literals and the filter error degree"
(P3:3170-3181: the final pass's running time is `c₅·(n+1)^{D₅}` uniformly over the call family). `S6Uni` asks, at
the parts of `finalPassClose4` (the `coreGenJ` over the four pool writers `Wr`, S4 v2 `XfR`, the bridge, the front,
X6's out machine), for degrees `Dg l fe` and coefficients `Cg l fe F` above every part's own:

* the degrees are read off by `rfl` (`frontOfHalves_Df/Dw`, `thrHalf_Dt`, `coreB3J`'s `Dcc = L.Dc`, `bridgeT_Dc/Dt/
  Dp/Do`, `XfR_Dt/Dp/Do/Dc`, `outGen_D`) and summed in **`DgU`**;
* the coefficients do not depend on `(kclk, coef, A, a)` (every part's coefficient is a closed term in `l`, `F` and the
  layout, `rfl`), so **`CgU`** sums them at the parameters `(0, 0, 0, 0)`;
* **`hU4 Wr`**: the bundle, generic in the pool writers `Wr`.

Paper quantity of the main type: the final pass's degree and coefficient, uniform over the call family
(P3:3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.HU

open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.WireExponent3_5.FinalPass.Close NearCubicWires.WireExponent3_5.FinalPass.Close2

variable (Wr : ∀ l : Literals, Core.CoreWritersJ l)

/-- S4 v2's size exponent at `(l, fe)`. -/
noncomputable abbrev Zx (l : Literals) (fe : ℕ) : ℕ :=
  Sd.R.ZXe l fe PrimT.S3.symPtEval (DszOf UnionMachine.SymSize.symSize_poly l) (DtzOf l)

/-- **The degrees' bound** on `(l, fe)`: the front's two, the bridge's three, the out machine's. -/
noncomputable def DgU (l : Literals) (fe : ℕ) : ℕ :=
  (S5T.Dl l + 1) + 3 * Zx l fe + Core.DcoreJ (Wr l) fe + Sd.R.ZTe l fe + 4 * Zx l fe +
    (2 * Zx l fe + Sd.budD (TabW.E2 F5c (Zx l fe)) (Zx l fe) (Zx l fe) PrimAsm.ThrData.thrDataStage2.Dc +
      3 * Zx l fe) + 2

/-- **The coefficients' bound** on `(l, F)`: every part's coefficient at the parameters `(0, 0, 0, 0)`. -/
noncomputable def CgU (l : Literals) (_fe : ℕ) (F : GateFree l) : ℕ :=
  (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
      Out.mOut l F 0 0 0 0 h00).Cf +
    (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
      Out.mOut l F 0 0 0 0 h00).Cw +
    (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00
      (XfR F5c UnionMachine.SymSize.symSize_poly l F 0 0 0 0 h00)).Ct +
    (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00
      (XfR F5c UnionMachine.SymSize.symSize_poly l F 0 0 0 0 h00)).Cp +
    (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00
      (XfR F5c UnionMachine.SymSize.symSize_poly l F 0 0 0 0 h00)).Co + Out.Gen.Cout

/-- The degrees below `DgU`. -/
theorem hD4 (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Df ≤ DgU Wr l F.filterErrDeg ∧
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Dw ≤ DgU Wr l F.filterErrDeg ∧
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
        (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Dt ≤ DgU Wr l F.filterErrDeg ∧
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
        (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Dp ≤ DgU Wr l F.filterErrDeg ∧
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
        (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Do ≤ DgU Wr l F.filterErrDeg ∧
      (OF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut outG l F kclk coef A a ha).D ≤ DgU Wr l F.filterErrDeg := by
  have eDf : (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
      (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Df =
      max (S5T.Dl l + 1) (max (3 * Zx l F.filterErrDeg)
        (max (S5T.Dl l + 1) (Core.DcoreJ (Wr l) F.filterErrDeg))) := rfl
  have eDw : (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
      (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Dw = Sd.R.ZTe l F.filterErrDeg := rfl
  have eDt : (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
      (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Dt = 3 * Zx l F.filterErrDeg := rfl
  have eDp : (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
      (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Dp = 4 * Zx l F.filterErrDeg := rfl
  have eDo : (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
      (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Do =
      2 * Zx l F.filterErrDeg + Sd.budD (TabW.E2 F5c (Zx l F.filterErrDeg)) (Zx l F.filterErrDeg)
        (Zx l F.filterErrDeg) PrimAsm.ThrData.thrDataStage2.Dc + 3 * Zx l F.filterErrDeg := rfl
  have eD : (OF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
      (Core.coreGenJ Wr S5T.mThrL) Out.mOut outG l F kclk coef A a ha).D = 2 := rfl
  rw [eDf, eDw, eDt, eDp, eDo, eD]
  unfold DgU
  refine ⟨max_le (by omega) (max_le (by omega) (max_le (by omega) (by omega))), by omega, by omega, by omega,
    by omega, by omega⟩

set_option maxHeartbeats 4000000 in
/-- The coefficients below `CgU`. -/
theorem hC4 (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Cf ≤ CgU Wr l F.filterErrDeg F ∧
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Cw ≤ CgU Wr l F.filterErrDeg F ∧
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
        (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Ct ≤ CgU Wr l F.filterErrDeg F ∧
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
        (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Cp ≤ CgU Wr l F.filterErrDeg F ∧
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
        (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Co ≤ CgU Wr l F.filterErrDeg F ∧
      (OF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut outG l F kclk coef A a ha).C ≤ CgU Wr l F.filterErrDeg F := by
  have e1 : (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
      (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Cf =
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00).Cf := rfl
  have e2 : (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
      (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha).Cw =
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00).Cw := rfl
  have e3 : (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
      (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Ct =
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00
        (XfR F5c UnionMachine.SymSize.symSize_poly l F 0 0 0 0 h00)).Ct := rfl
  have e4 : (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
      (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Cp =
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00
        (XfR F5c UnionMachine.SymSize.symSize_poly l F 0 0 0 0 h00)).Cp := rfl
  have e5 : (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F kclk coef A a ha
      (XfR F5c UnionMachine.SymSize.symSize_poly l F kclk coef A a ha)).Co =
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut l F 0 0 0 0 h00
        (XfR F5c UnionMachine.SymSize.symSize_poly l F 0 0 0 0 h00)).Co := rfl
  have e6 : (OF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
      (Core.coreGenJ Wr S5T.mThrL) Out.mOut outG l F kclk coef A a ha).C = Out.Gen.Cout := rfl
  rw [e1, e2, e3, e4, e5, e6]
  unfold CgU
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The uniformity bundle at `finalPassClose4`'s parts** (X6). -/
noncomputable def hU4 :
    Assembly.S6Uni Sw0 (XfR F5c UnionMachine.SymSize.symSize_poly)
      (bTf (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL) Out.mOut)
      (frontF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l))
        (Core.coreGenJ Wr S5T.mThrL) Out.mOut)
      (oF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
        Out.mOut)
      (scF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
        Out.mOut)
      (OF (XfR F5c UnionMachine.SymSize.symSize_poly) (fun l => Core.mCoreOfJ (Wr l)) (Core.coreGenJ Wr S5T.mThrL)
        Out.mOut outG) where
  Dg := DgU Wr
  Cg := CgU Wr
  hD := hD4 Wr
  hC := hC4 Wr

/-- **The final pass from the four pool writers alone** (`finalPassClose4 Wr (hU4 Wr)`). -/
noncomputable def finalPassClose5 : FinalPassStage1.StageT := Close4.finalPassClose4 Wr (hU4 Wr)

end NearCubicWires.WireExponent3_5.FinalPass.Out.HU

end
