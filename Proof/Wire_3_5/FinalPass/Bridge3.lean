import Lean
import Proof.Wire_3_5.FinalPass.Bridge2
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.AssemblyDock3
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.FinalPass.SeamsOut2
import Proof.Wire_3_5.FinalPass.SeamsProg
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.FinalPass.SeamsPt
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.FinalPass.Bridge1


noncomputable section
set_option maxRecDepth 4096


/-! # BridgeT, part 3: the seeds phase `bridgeT`, the halves' layout and rooms

* **`bridgeT X mT mC mI K0 D0 : SeedsProg4`** (finalPass_of3's `bridgeT` at the rooms and the register need): S4 on
  the shared bank (`bridge_run`), register capacity `max X.Kc K0 · N^{max X.Dc D0}`, the idle room kept;
* **`bridgeExt : LayExt4`**: the halves' scratch sets are the THR and core rooms (register-length tapes off the input,
  the words and the numbers);
* **`bridgeRoom : HalfRoom2 (layOf4 (bridgeT …) bridgeExt) mT mC`** (both halves' rooms);
* `bridgeT_Kc`, `bridgeT_Dc`, `bridgeT_Dt/Dp/Do/Ct/Cp/Co` (S4's constants, `+ 2` on `Co`: the uniformity `S6Uni`).

Paper quantity of the main type: the seeds phase's printed numerator and denominator (P3:3170-3181). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Bridge
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.BlockPlatform
open NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass.Seams
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.Assembly NearCubicWires.WireExponent3_5.FinalPass.Bank

section Br3
variable {l : Literals} {F : GateFree l} {kclk coef A a : ℕ} {ha : a ≤ kclk + 1} {Sw : SymWords}
  (X : SeedsWS2 l F kclk coef A a ha Sw) (mT mC mI K0 D0 : ℕ)

theorem idle_off (j : Fin (tB X.L.ns X.L.nr mT mC mI)) (hj : idleB X.L.ns X.L.nr mT mC mI j = true) :
    regB X.L.ns X.L.nr mT mC mI j = false ∧ (∀ k, j ≠ e4 X.L.ns X.L.nr mT mC mI (sTape (X.L.wdS k))) ∧
      j ≠ e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN) ∧ j ≠ e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD) := by
  have hjv : 1 + (X.L.ns + 2 + X.L.nr) + mT + mC ≤ j.val := by simpa [idleB] using hj
  refine ⟨?_, fun k e => ?_, fun e => ?_, fun e => ?_⟩
  · unfold regB; simp only [decide_eq_false_iff_not]; omega
  · have h1 := congrArg Fin.val e; rw [e4_val] at h1
    have := (sTape (nr := X.L.nr) (X.L.wdS k)).isLt; omega
  · have h1 := congrArg Fin.val e; rw [e4_val] at h1
    have := (sTape (nr := X.L.nr) X.L.sN).isLt; omega
  · have h1 := congrArg Fin.val e; rw [e4_val] at h1
    have := (sTape (nr := X.L.nr) X.L.sD).isLt; omega

/-- **BridgeT**: S4 as the seeds phase on the shared bank. -/
noncomputable def bridgeT : SeedsProg4 l F kclk coef A a ha Sw where
  t := tB X.L.ns X.L.nr mT mC mI
  wd := fun k => e4 X.L.ns X.L.nr mT mC mI (sTape (X.L.wdS k))
  tN := e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN)
  tD := e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD)
  reg := regB X.L.ns X.L.nr mT mC mI
  Kc := max X.Kc K0
  Dc := max X.Dc D0
  s := _
  M := Composition.machine (cellP X.L.ns X.L.nr mT mC mI).compile (RecoveryFocus.machine (e4 X.L.ns X.L.nr mT mC mI) X.M)
  tab := X.tab
  pt := X.pt
  ov := fun r => X.ov r + 2
  Cp := X.Cp
  Dp := X.Dp
  Ct := X.Ct
  Dt := X.Dt
  Co := X.Co + 2
  Do := X.Do
  pt_le := X.pt_le
  tab_le := X.tab_le
  ov_le := ov_le2 X
  idle := idleB X.L.ns X.L.nr mT mC mI
  idleOff := idle_off X mT mC mI
  exitA := exitB X mT mC mI K0 D0
  run := fun H Ab W hF hW r => bridge_run X mT mC mI K0 D0 H Ab W hF hW r

/-- **The halves' layout inside the seeds phase's**: the scratch sets are the rooms. -/
def bridgeExt : LayExt4 l F kclk coef A a ha Sw (bridgeT X mT mC mI K0 D0) where
  ht := by show 1 ≤ tB X.L.ns X.L.nr mT mC mI; unfold tB; omega
  thrSc := thrB X.L.ns X.L.nr mT mC mI
  coreSc := coreB X.L.ns X.L.nr mT mC mI
  wdInj := fun a b h => X.L.wdInj (PrimAsm.DockW.sTape_inj (e4_inj X.L.ns X.L.nr mT mC mI h))
  hND := fun h => X.L.nd (PrimAsm.DockW.sTape_inj (e4_inj X.L.ns X.L.nr mT mC mI h))
  wdN := fun k h => X.L.wdN k (PrimAsm.DockW.sTape_inj (e4_inj X.L.ns X.L.nr mT mC mI h))
  wdD := fun k h => X.L.wdD k (PrimAsm.DockW.sTape_inj (e4_inj X.L.ns X.L.nr mT mC mI h))
  in0 := fun k => by show (e4 X.L.ns X.L.nr mT mC mI _).val ≠ 0; rw [e4_val]; omega
  inN := by show (e4 X.L.ns X.L.nr mT mC mI _).val ≠ 0; rw [e4_val]; omega
  inD := by show (e4 X.L.ns X.L.nr mT mC mI _).val ≠ 0; rw [e4_val]; omega
  reg0 := by
    show regB X.L.ns X.L.nr mT mC mI ⟨0, by unfold tB; omega⟩ = true
    unfold regB; simp
  thrReg := fun j h => by
    show regB X.L.ns X.L.nr mT mC mI j = true
    have := j.isLt
    simp only [thrB, decide_eq_true_eq] at h
    unfold regB; simp only [decide_eq_true_eq]; omega
  coreReg := fun j h => by
    show regB X.L.ns X.L.nr mT mC mI j = true
    simp only [coreB, decide_eq_true_eq] at h
    unfold regB; simp only [decide_eq_true_eq]; omega
  thrOff := fun j h => by
    simp only [thrB, decide_eq_true_eq] at h
    refine ⟨by omega, fun k e => ?_, fun e => ?_, fun e => ?_⟩
    · have h1 := congrArg Fin.val e; rw [show (bridgeT X mT mC mI K0 D0).wd k =
        e4 X.L.ns X.L.nr mT mC mI (sTape (X.L.wdS k)) from rfl, e4_val] at h1
      have := (sTape (nr := X.L.nr) (X.L.wdS k)).isLt; omega
    · have h1 := congrArg Fin.val e; rw [show (bridgeT X mT mC mI K0 D0).tN =
        e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN) from rfl, e4_val] at h1
      have := (sTape (nr := X.L.nr) X.L.sN).isLt; omega
    · have h1 := congrArg Fin.val e; rw [show (bridgeT X mT mC mI K0 D0).tD =
        e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD) from rfl, e4_val] at h1
      have := (sTape (nr := X.L.nr) X.L.sD).isLt; omega
  coreOff := fun j h => by
    simp only [coreB, decide_eq_true_eq] at h
    refine ⟨by omega, fun k e => ?_, fun e => ?_, fun e => ?_⟩
    · have h1 := congrArg Fin.val e; rw [show (bridgeT X mT mC mI K0 D0).wd k =
        e4 X.L.ns X.L.nr mT mC mI (sTape (X.L.wdS k)) from rfl, e4_val] at h1
      have := (sTape (nr := X.L.nr) (X.L.wdS k)).isLt; omega
    · have h1 := congrArg Fin.val e; rw [show (bridgeT X mT mC mI K0 D0).tN =
        e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sN) from rfl, e4_val] at h1
      have := (sTape (nr := X.L.nr) X.L.sN).isLt; omega
    · have h1 := congrArg Fin.val e; rw [show (bridgeT X mT mC mI K0 D0).tD =
        e4 X.L.ns X.L.nr mT mC mI (sTape X.L.sD) from rfl, e4_val] at h1
      have := (sTape (nr := X.L.nr) X.L.sD).isLt; omega
  disj := fun j h => by
    simp only [thrB, decide_eq_true_eq] at h
    show coreB X.L.ns X.L.nr mT mC mI j = false
    unfold coreB; simp only [decide_eq_false_iff_not]; omega

/-- **Both halves' rooms in the seeds phase's bank.** -/
def bridgeRoom : HalfRoom2 (layOf4 (bridgeT X mT mC mI K0 D0) (bridgeExt X mT mC mI K0 D0)) mT mC where
  thrE := ⟨thrT X.L.ns X.L.nr mT mC mI, fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [thrT] at this; omega)⟩
  thrE_sc := fun i => by
    show thrB X.L.ns X.L.nr mT mC mI (thrT X.L.ns X.L.nr mT mC mI i) = true
    have := i.isLt; unfold thrB thrT; simp only [decide_eq_true_eq]; omega
  coreE := ⟨coreT X.L.ns X.L.nr mT mC mI, fun a b h => Fin.ext (by
    have := congrArg Fin.val h; simp only [coreT] at this; omega)⟩
  coreE_sc := fun i => by
    show coreB X.L.ns X.L.nr mT mC mI (coreT X.L.ns X.L.nr mT mC mI i) = true
    have := i.isLt; unfold coreB coreT; simp only [decide_eq_true_eq]; omega


end Br3

end NearCubicWires.WireExponent3_5.FinalPass.Bridge

end
