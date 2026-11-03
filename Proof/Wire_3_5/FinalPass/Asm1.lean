import Lean
import Proof.Wire_3_5.FinalPass.Front1
import Proof.Wire_3_5.FinalPass.S5TInst
import Proof.Wire_3_5.FinalPass.S6Iface
import Proof.Wire_3_5.FinalPass.SdI11
import Proof.Wire_3_5.Primitive.SeedFix.S3Big12
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.AssemblyDock3
import Proof.Wire_3_5.FinalPass.Bridge3
import Proof.Wire_3_5.FinalPass.SdI3
import Proof.Wire_3_5.FinalPass.SeamsHalves
import Proof.Wire_3_5.FinalPass.SeamsOut2
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.ThrSz6
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Primitive.Writers.S5SeamB2
import Proof.Wire_3_5.Primitive.SeedFix.ThrNumsPoly
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.FinalPass.Asm1Base


noncomputable section
set_option maxRecDepth 120000


/-! # The final pass's assembly: the parts on `finalPass_of3` (P3:3044-3048, 3170-3181)

The finish term's parts from the open producers (SYM size `hS`, #124; the core half `core : CoreHalfGen2`, PA2; the out
machine `outG : OutGen mOut`, X6), at the SYM words `Sw0` (the `symPtEval`) and S4's tables producers `F5`:

* **`Xf`**: S4 (`Sd.seedsWS2Of`) at the size polynomials (`symOK` from `hS`; `thrOK` from `ThrSz.thrSize_poly`); the
  parts below are generic in S4 `X` (S4's constants are rebased on `CallIndexR` in S4 v2);
* **`bTf`**: BridgeT at the rooms `mThrL l`, `mCore l`, `mOut + 1` and the halves' register need (`K0f`, `D0f`);
* **`frontF`**: the front from the THR half (`S5T.thrHalfGen`) and `core` at `bridgeExt`/`bridgeRoom`;
* **`oF`**, **`scF`**, **`eF`**, **`OF`**: the out machine on the idle room (`o` its first tape, the rest scratch);
* **`finalPassAsm`**: `finalPass_of_s6` at S6's deliverable `S6Out` for these parts: `∀ l, FinalPassLeaf l`.

Paper quantity of the main type: `FinalPassLeaf l`, the final pass of `lem:primitive` (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Seams NearCubicWires.WireExponent3_5.FinalPass.PlanFP
open NearCubicWires.WireExponent3_5.PrimAsm.Plan

section Sizes
variable (hS : ∀ l : Literals, ∃ Dsz : ℕ, ∀ F : GateFree l, ∃ Csz : ℕ, ∀ (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval Csz Dsz)

/-- The SYM size's degree (on `l`). -/
noncomputable def DszOf (l : Literals) : ℕ := Classical.choose (hS l)

/-- The SYM size's coefficient (on `F`). -/
noncomputable def CszOf (l : Literals) (F : GateFree l) : ℕ := Classical.choose (Classical.choose_spec (hS l) F)

theorem symOK (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    Sd.SymSizeOK l F kclk coef A a ha PrimT.S3.symPtEval (CszOf hS l F) (DszOf hS l) :=
  Classical.choose_spec (Classical.choose_spec (hS l) F) kclk coef A a ha

end Sizes

/-- The THR size's degree (on `l`). -/
noncomputable def DtzOf (l : Literals) : ℕ := Classical.choose (ThrSz.thrSize_poly l (PrimT.W6.thrNumsPoly l))

/-- The THR size's coefficient (on `F`). -/
noncomputable def CtzOf (l : Literals) (F : GateFree l) : ℕ :=
  Classical.choose (Classical.choose_spec (ThrSz.thrSize_poly l (PrimT.W6.thrNumsPoly l)) F)

theorem thrOK (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    Sd.ThrSizeOK l F kclk coef A a ha (CtzOf l F) (DtzOf l) :=
  fun n hs _ ha' Cs carriers translation hcar hd =>
    Classical.choose_spec (Classical.choose_spec (ThrSz.thrSize_poly l (PrimT.W6.thrNumsPoly l)) F) kclk coef A a ha
      n hs ha' Cs carriers translation hcar hd

section S4v1

end S4v1

section Parts
variable (X : ∀ (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1),
    SeedsWS2 l F kclk coef A a ha Sw0)
  (mCore : Literals → ℕ) (core : Bank.CoreHalfGen2 Sw0 S5T.mThrL mCore) (mOut : ℕ) (outG : Bank.OutGen mOut)

/-- The halves' register coefficient. -/
noncomputable def K0f (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : ℕ :=
  max (S5T.thrHalfGen Sw0 mCore l F kclk coef A a ha).K (core l F kclk coef A a ha).K

/-- The halves' register degree. -/
noncomputable def D0f (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) : ℕ :=
  max (S5T.thrHalfGen Sw0 mCore l F kclk coef A a ha).D (core l F kclk coef A a ha).D

/-- **BridgeT** at the rooms and the halves' register need. -/
noncomputable def bTf (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (X : SeedsWS2 l F kclk coef A a ha Sw0) : SeedsProg4 l F kclk coef A a ha Sw0 :=
  Bridge.bridgeT X (S5T.mThrL l) (mCore l) (mOut + 1) (K0f mCore core l F kclk coef A a ha)
    (D0f mCore core l F kclk coef A a ha)

/-- The seeds phase's bank at `Xf`. -/
noncomputable abbrev Yf (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    SeedsProg4 l F kclk coef A a ha Sw0 :=
  bTf mCore core mOut l F kclk coef A a ha (X l F kclk coef A a ha)

/-- The halves' layout at `Xf`. -/
noncomputable abbrev Ef (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    Assembly.LayExt4 l F kclk coef A a ha Sw0 (Yf X mCore core mOut l F kclk coef A a ha) :=
  Bridge.bridgeExt (X l F kclk coef A a ha) (S5T.mThrL l) (mCore l) (mOut + 1)
    (K0f mCore core l F kclk coef A a ha) (D0f mCore core l F kclk coef A a ha)

/-- The halves' rooms at `Xf`. -/
noncomputable abbrev Rf (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    Bank.HalfRoom2 (Assembly.layOf4 (Yf X mCore core mOut l F kclk coef A a ha)
      (Ef X mCore core mOut l F kclk coef A a ha)) (S5T.mThrL l) (mCore l) :=
  Bridge.bridgeRoom (X l F kclk coef A a ha) (S5T.mThrL l) (mCore l) (mOut + 1)
    (K0f mCore core l F kclk coef A a ha) (D0f mCore core l F kclk coef A a ha)

/-- **The front** from the two halves. -/
noncomputable def frontF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    Assembly.FrontPh3 l F kclk coef A a ha Sw0 (Yf X mCore core mOut l F kclk coef A a ha) :=
  Bridge.frontOfHalves (Yf X mCore core mOut l F kclk coef A a ha) (Ef X mCore core mOut l F kclk coef A a ha)
    ((S5T.thrHalfGen Sw0 mCore l F kclk coef A a ha).half _ (Rf X mCore core mOut l F kclk coef A a ha)
      ((le_max_left _ _).trans (le_max_right _ _)) ((le_max_left _ _).trans (le_max_right _ _)))
    ((core l F kclk coef A a ha).half _ (Rf X mCore core mOut l F kclk coef A a ha)
      ((le_max_right _ _).trans (le_max_right _ _)) ((le_max_right _ _).trans (le_max_right _ _)))

/-- **The out machine's output tape**: the idle room's first tape. -/
noncomputable def oF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    Fin (Yf X mCore core mOut l F kclk coef A a ha).t :=
  Bridge.idleT (X l F kclk coef A a ha).L.ns (X l F kclk coef A a ha).L.nr (S5T.mThrL l) (mCore l)
    (mOut + 1) ⟨0, by omega⟩

/-- The out machine's scratch: the rest of the idle room. -/
noncomputable def scF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)
    (j : Fin (Yf X mCore core mOut l F kclk coef A a ha).t) : Bool :=
  decide (Bridge.idleB (X l F kclk coef A a ha).L.ns (X l F kclk coef A a ha).L.nr (S5T.mThrL l)
    (mCore l) (mOut + 1) j = true ∧ j ≠ oF X mCore core mOut l F kclk coef A a ha)

/-- The out machine's room in the scratch. -/
noncomputable def eF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    Fin mOut ↪ Fin (Yf X mCore core mOut l F kclk coef A a ha).t :=
  ⟨fun i => Bridge.idleT (X l F kclk coef A a ha).L.ns (X l F kclk coef A a ha).L.nr (S5T.mThrL l)
    (mCore l) (mOut + 1) ⟨i.val + 1, by omega⟩, fun a b h => Fin.ext (by
      have := congrArg Fin.val h; simp only [Bridge.idleT] at this; omega)⟩

theorem idle_idleT (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (i : Fin (mOut + 1)) :
    Bridge.idleB (X l F kclk coef A a ha).L.ns (X l F kclk coef A a ha).L.nr (S5T.mThrL l) (mCore l)
      (mOut + 1) (Bridge.idleT (X l F kclk coef A a ha).L.ns (X l F kclk coef A a ha).L.nr
        (S5T.mThrL l) (mCore l) (mOut + 1) i) = true := by
  unfold Bridge.idleB Bridge.idleT; simp

theorem hoF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    (oF X mCore core mOut l F kclk coef A a ha).val ≠ 0 := by
  unfold oF Bridge.idleT; simp only; omega

theorem hoIF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    (Yf X mCore core mOut l F kclk coef A a ha).idle (oF X mCore core mOut l F kclk coef A a ha) = true :=
  idle_idleT X mCore mOut l F kclk coef A a ha _

theorem hscF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    ∀ j, scF X mCore core mOut l F kclk coef A a ha j = true →
      (Yf X mCore core mOut l F kclk coef A a ha).idle j = true := fun j h => by
  unfold scF at h
  simp only [decide_eq_true_eq] at h
  exact h.1

/-- **The out machine** on the idle room. -/
noncomputable def OF (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) :
    OutMachine2 (Yf X mCore core mOut l F kclk coef A a ha).t (oF X mCore core mOut l F kclk coef A a ha)
      (Yf X mCore core mOut l F kclk coef A a ha).tN (Yf X mCore core mOut l F kclk coef A a ha).tD
      (scF X mCore core mOut l F kclk coef A a ha) :=
  outG _ _ _ _ _ (eF X mCore core mOut l F kclk coef A a ha)
    (fun i => by
      unfold scF eF
      simp only [Function.Embedding.coeFn_mk, decide_eq_true_eq]
      refine ⟨idle_idleT X mCore mOut l F kclk coef A a ha _, fun e => ?_⟩
      have := congrArg Fin.val e
      simp only [oF, Bridge.idleT] at this
      omega)
    (fun i => by
      have hI := (Bridge.idle_off (X l F kclk coef A a ha) (S5T.mThrL l) (mCore l) (mOut + 1) _
        (idle_idleT X mCore mOut l F kclk coef A a ha ⟨i.val + 1, by omega⟩)).2
      refine ⟨fun e => ?_, hI.2.1, hI.2.2⟩
      have := congrArg Fin.val e
      simp only [eF, oF, Bridge.idleT, Function.Embedding.coeFn_mk] at this
      omega)
    (Bridge.idle_off (X l F kclk coef A a ha) (S5T.mThrL l) (mCore l) (mOut + 1) _
      (hoIF X mCore core mOut l F kclk coef A a ha)).2.2.1
    (Bridge.idle_off (X l F kclk coef A a ha) (S5T.mThrL l) (mCore l) (mOut + 1) _
      (hoIF X mCore core mOut l F kclk coef A a ha)).2.2.2
    (fun h => (X l F kclk coef A a ha).L.nd (PrimAsm.DockW.sTape_inj (Bridge.e4_inj _ _ _ _ _ h)))

/-- **The final pass from its producers** and S6's deliverable for these parts. -/
noncomputable def finalPassAsm
    (S : Assembly.S6Out Sw0 X (bTf mCore core mOut) (frontF X mCore core mOut) (oF X mCore core mOut)
      (scF X mCore core mOut) (OF X mCore core mOut outG)) :
    (l : Literals) → FinalPassLeaf l :=
  Assembly.finalPass_of_s6 Sw0 X (bTf mCore core mOut) (frontF X mCore core mOut) (oF X mCore core mOut)
    (hoF X mCore core mOut) (scF X mCore core mOut) (hoIF X mCore core mOut)
    (hscF X mCore core mOut) (OF X mCore core mOut outG) S

/-- **The final pass from its producers**, S6's target and the uniformity bundle. -/
noncomputable def finalPassAsm2
    (s6 : Assembly.S6Target Sw0 X (bTf mCore core mOut) (frontF X mCore core mOut)
      (oF X mCore core mOut) (scF X mCore core mOut) (OF X mCore core mOut outG))
    (hU : Assembly.S6Uni Sw0 X (bTf mCore core mOut) (frontF X mCore core mOut)
      (oF X mCore core mOut) (scF X mCore core mOut) (OF X mCore core mOut outG)) :
    (l : Literals) → FinalPassLeaf l :=
  finalPassAsm X mCore core mOut outG (s6 hU)

end Parts

end NearCubicWires.WireExponent3_5.FinalPass.Finish

end
