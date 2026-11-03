import Lean
import Proof.Wire_3_5.UnionMachine.NumsG1
import Proof.Wire_3_5.UnionMachine.NumsW2
import Proof.Wire_3_5.UnionMachine.NumsC7
import Proof.Wire_3_5.FinalPass.SWParts
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR12
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.SeamsProg3
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Foundations.OutMachineJoinG
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsC6
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsG2Base


noncomputable section
set_option maxRecDepth 120000


/-! # SWg, part 2: the gate tables' writer `swG x hx l : SWParts.SWgT l` (x ≥ DT + 3)

P3:3049-3050, 3170-3178 (the `symWords`, kind `0`: the SYM slots `16 … 19`, `Corner.gatesW (tabH G_j) G_j`): at a SYM
request, from the core's blank entry, on NW's bank:

1. phase (c)'s program `cProg` (`cRun`: `n`, the mode, `e`, `T_f`), NW (a)'s `prepW` (`width_run`, `tapes_run`);
2. PA's data stage docked (`dockG`): the tables on the slot tapes `tmapA (iSym j)` (blank past the tuple);
3. `fixW`: each blank slot tape to `[false]` (`fix1_spec`), the slot tapes ARE the outputs.

Every register ends `0` (the stash consumed the roles); the other streams are the data stage's residue, the stash
and stream `1`. The capacity `K_g·X^{D_g}`, steps and residue `C_g·X^{D_g'}`, the exponents functions of `fe`.

* `swg_word` (the slots are `gatesW (tabH (gatesJ k j)) (gatesJ k j)`: `symWords_idx`), `sOutG`, `fixW`, `fix_run`,
  constants, **`gRun`**, **`swG`**.

Paper quantities of the main type: the SYM call's bottom gates' tables (the `symWords`, kind `0`). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.FinalPass.Finish (symSlot sw0_nw)
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g)

section Link
variable (l : Literals) (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

/-- **The gate tables' slots**: word `j` of `SWgT` is `gatesW (tabH (gatesJ k j)) (gatesJ k j)`. -/
theorem swg_word {n a' : ℕ} (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩)
    (hs : (callInputs l F kclk coef A a ha).StarAt n) (j : Fin 4) :
    FinalPass.SWParts.swWs l 0 4 (by norm_num) F kclk coef A a ha
        ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ j =
      FinalPass.Corner.gatesW
        (PrimT.tabH (PrimT.S3.gatesJ (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) j))
        (PrimT.S3.gatesJ (FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers) j) := by
  have hv : (symSlot ⟨0 + j.val, by omega⟩).val = 16 + j.val := by simp [symSlot]
  have hj := j.isLt
  simp only [FinalPass.SWParts.swWs, FinalPass.Seams.frontWordsW2, FinalPass.Seams.frontWordsOfW2, dif_pos hs]
  split_ifs with h1 h2 h3
  · omega
  · omega
  · have e2 : (⟨(symSlot ⟨0 + j.val, by omega⟩).val - 16, h3⟩ : Fin 16) = PrimT.S3.wIdx 0 j :=
      Fin.ext (by show 16 + (0 + j.val) - 16 = 4 * 0 + j.val; omega)
    show PrimT.S3.symWords _ ⟨(symSlot ⟨0 + j.val, by omega⟩).val - 16, h3⟩ = _
    rw [e2, PrimT.S3.symWords_idx]
    rfl
  · exfalso
    have e3 : FinalPass.Finish.Sw0.nw = 16 := sw0_nw
    omega

end Link

section Consts
variable (l : Literals)

/-- SWg's capacity and step constants (the degrees functions of `fe`). -/
noncomputable def Kg (F : GateFree l) : ℕ := NumsC.KnC l F + KTZ l F + 100
noncomputable def Dg (fe : ℕ) : ℕ := NumsC.DnC l fe + FinalPass.Sd.R.ZTe l fe + 27
noncomputable def Csg (F : GateFree l) : ℕ :=
  NumsC.CsC l F + 4000 * 2 ^ 27 + 100 * (KTZ l F + 30) + Data.symCc * 82 ^ Data.symDc + 100
noncomputable def Dsg (fe : ℕ) : ℕ := NumsC.DsC l fe + FinalPass.Sd.R.ZTe l fe + 27 + 26 * Data.symDc

end Consts

/-- SWg's machine: `cProg ; prepW`, the data stage, `fixW`. -/
noncomputable def gM (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals) (F : GateFree l) :=
  Composition.machine (Composition.machine
    (WM.seq (NumsC.cProg x F.cr (FinalPass.Sd.R.KT l F) (FinalPass.Sd.R.ZT l F)) (prepW x hx)).toProg.compile
    (DataDock.dataDockM (nr := LNR) (tmapA x hx))) (fixW x hx).toProg.compile

section Gate
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals)

/-- **SWg's run at a SYM request.** -/
theorem gRun (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) {n a' : ℕ} (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedSymmetricThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call ⟨n, .sym, a', ha', Cs, carriers, translation⟩) (σ : St x)
    (hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)) (hsh : ∀ i, σ.sh i = 0) (hbl : ∀ i, i ≠ sIn x → σ.st i = [])
    (hv : ∀ q, σ.val q = 0) (hcell : σ.cell = false) :
    ∃ (τ : St x) (m : ℕ), m ≤ Csg l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Dsg l F.filterErrDeg ∧
      Step (gM x hx l F) m (wenc (Kg l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Dg l F.filterErrDeg) σ).H
        (wenc (Kg l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Dg l F.filterErrDeg) σ).A
        (wenc (Kg l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Dg l F.filterErrDeg) τ).H
        (wenc (Kg l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Dg l F.filterErrDeg) τ).A ∧
      (∀ k : Fin 4, τ.st (sOutG x hx k) = FinalPass.SWParts.swWs l 0 4 (by norm_num) F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ k) ∧
      τ.st (sIn x) = frame (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) ∧
      (∀ i, i ≠ sIn x → (∀ k, i ≠ sOutG x hx k) →
        (τ.st i).length ≤ Csg l F * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1) ^ Dsg l F.filterErrDeg) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  have hs : (callInputs l F kclk coef A a ha).StarAt n := hcall.2.2.2.2.2.1
  have hnw : n ≤ (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length := FinalPass.FpInLen.n_le_fpIn (l := l) (F := F) (kclk := kclk) (coef := coef) (A := A)
    (a := a) (ha := ha) ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + 1 := ⟨_, rfl⟩
  rw [← hXd]
  have hX1 : 1 ≤ X := by omega
  have hnX : n + 1 ≤ X := by omega
  obtain ⟨cap, hcapd⟩ : ∃ v, v = Kg l F * X ^ Dg l F.filterErrDeg := ⟨_, rfl⟩
  rw [← hcapd]
  have hDg : Dg l F.filterErrDeg = FinalPass.Sd.R.ZTe l F.filterErrDeg + 2 + FinalPass.Sd.R.ZTe l F.filterErrDeg + 27 :=
    rfl
  have hDsg : Dsg l F.filterErrDeg = FinalPass.Sd.R.ZTe l F.filterErrDeg + 2 + FinalPass.Sd.R.ZTe l F.filterErrDeg + 27 +
      26 * Data.symDc := rfl
  have hZT : FinalPass.Sd.R.ZT l F = FinalPass.Sd.R.ZTe l F.filterErrDeg := rfl
  have liftG : ∀ {d : ℕ}, d ≤ Dg l F.filterErrDeg → X ^ d ≤ X ^ Dg l F.filterErrDeg :=
    fun hd => Nat.pow_le_pow_right hX1 hd
  have liftS : ∀ {d : ℕ}, d ≤ Dsg l F.filterErrDeg → X ^ d ≤ X ^ Dsg l F.filterErrDeg :=
    fun hd => Nat.pow_le_pow_right hX1 hd
  have hGS : X ^ Dg l F.filterErrDeg ≤ X ^ Dsg l F.filterErrDeg := liftS (by rw [hDg, hDsg]; omega)
  have hXG : X ≤ X ^ Dg l F.filterErrDeg := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ _ := liftG (by rw [hDg]; omega)
  -- the width and `T_f`
  obtain ⟨W, hWd⟩ : ∃ v, v = wOf (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length n := ⟨_, rfl⟩
  have hW27 : W ≤ 27 * X ^ 26 := by
    rw [hWd]; unfold wOf
    have h1 : (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length ≤ X ^ 26 := by
      calc (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length ≤ X ^ 1 := by rw [pow_one]; omega
        _ ≤ X ^ 26 := Nat.pow_le_pow_right hX1 (by omega)
    have h2 : (n + 1) ^ 26 ≤ X ^ 26 := Nat.pow_le_pow_left (by omega) 26
    have h3 : 1 ≤ X ^ 26 := Nat.one_le_pow _ _ (by omega)
    omega
  have hWG : W ≤ 27 * X ^ Dg l F.filterErrDeg := le_trans hW27 (Nat.mul_le_mul_left _ (liftG (by rw [hDg]; omega)))
  have hTX : FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ ≤ KTZ l F * X ^ Dg l F.filterErrDeg := by
    show FinalPass.Sd.R.KT l F * (n + 2) ^ FinalPass.Sd.R.ZT l F ≤ _
    have h1 := NumsC.npow_le n X (FinalPass.Sd.R.ZT l F) hnX
    have h2 : X ^ FinalPass.Sd.R.ZT l F ≤ X ^ Dg l F.filterErrDeg := liftG (by rw [hZT, hDg]; omega)
    unfold KTZ; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (le_trans h1 (Nat.mul_le_mul_left _ h2))
  have heN : eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ ≤ n := Nat.sub_le _ _
  have hKg : Kg l F * X ^ Dg l F.filterErrDeg = NumsC.KnC l F * X ^ Dg l F.filterErrDeg +
      KTZ l F * X ^ Dg l F.filterErrDeg + 100 * X ^ Dg l F.filterErrDeg := by unfold Kg; ring
  have capC : NumsC.KnC l F * X ^ NumsC.DnC l F.filterErrDeg ≤ cap := by
    rw [hcapd, hKg]
    have := Nat.mul_le_mul_left (NumsC.KnC l F) (liftG (d := NumsC.DnC l F.filterErrDeg) (by rw [hDg]; unfold NumsC.DnC; omega))
    omega
  have capW : W + 2 * (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + n + 2 ≤ cap := by rw [hcapd, hKg]; omega
  have capT : n + W + eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ ≤ cap := by
    rw [hcapd, hKg]; omega
  -- 1: (c)'s program
  have hm0 : mOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ = 0 := rfl
  obtain ⟨c1, e1, hc1⟩ := NumsC.cRun x l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ cap (by rw [← hXd]; exact capC) σ
    ⟨hin, hsh, hbl, hv, hcell⟩
  rw [← hXd] at hc1
  rw [hm0] at e1
  obtain ⟨σ1, hσ1⟩ : ∃ s, s = ((((σ.seth (sIn x) 0).setv rN n).setv rM 0).setv rE (eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)).setv
      rT (FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) := ⟨_, rfl⟩
  rw [← hσ1] at e1
  have s1 : σ1.st = σ.st := by rw [hσ1]; rfl
  have sh1 : ∀ i, σ1.sh i = 0 := fun i => by
    rw [hσ1]; simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]; split_ifs <;> simp [hsh]
  have v1 : ∀ q, σ1.val q = if q = rT then FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ else
      if q = rE then eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ else if q = rN then n else 0 := by
    intro q; rw [hσ1]; simp only [WState.setv_val, WState.seth_val, Function.update_apply]
    by_cases a1 : q = rT
    · rw [if_pos a1, if_pos a1]
    · rw [if_neg a1, if_neg a1]
      by_cases a2 : q = rE
      · rw [if_pos a2, if_pos a2]
      · rw [if_neg a2, if_neg a2]
        by_cases a3 : q = rM
        · rw [if_pos a3, if_neg (by rw [a3]; decide)]
        · rw [if_neg a3]
          by_cases a4 : q = rN
          · rw [if_pos a4, if_pos a4]
          · rw [if_neg a4, if_neg a4, hv]
  have gv : ∀ j : Fin 10, σ1.val (g j) = 0 := fun j => by
    rw [v1, if_neg (NumsC.g_ne j).2.2.2, if_neg (NumsC.g_ne j).2.2.1, if_neg (NumsC.g_ne j).1]
  -- 2: the width
  obtain ⟨c2, e2, hc2⟩ := width_run x cap (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) n σ1 (by rw [s1]; exact hin) (sh1 _)
    (by rw [v1, if_neg (by decide), if_neg (by decide), if_pos rfl]) gv (by rw [← hWd]; omega)
  rw [← hWd] at e2
  -- 3: the tapes and the stash
  obtain ⟨τ1, c3, e3, hPD, hc3⟩ := tapes_run x hx cap (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) n W (eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩)
    (FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) (σ1.setv (g 2) W) (by rw [WState.setv_st, s1]; exact hin)
    (fun i hi => by rw [WState.setv_st, s1]; exact hbl i hi) (fun i => by rw [WState.setv_sh]; exact sh1 i)
    (by rw [WState.setv_cell, hσ1]; exact hcell)
    (by rw [WState.setv_val, Function.update_of_ne (show rN ≠ g 2 by decide), v1, if_neg (by decide), if_neg (by decide),
      if_pos rfl])
    (by rw [WState.setv_val, Function.update_self])
    (by rw [WState.setv_val, Function.update_of_ne (show rE ≠ g 2 by decide), v1, if_neg (by decide), if_pos rfl])
    (by rw [WState.setv_val, Function.update_of_ne (show rT ≠ g 2 by decide), v1, if_pos rfl])
    (fun q a1 a2 a3 a4 => by rw [WState.setv_val, Function.update_of_ne a4, v1, if_neg a3, if_neg a2, if_neg a1])
    capT
  rw [hWd] at hPD
  -- 4: the data stage
  obtain ⟨tout, sD, hinw, hS, hSb, hlen⟩ := dockG l F kclk coef A a ha x hx ha' Cs carriers translation hcall cap
    (eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) (FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩) τ1 hPD
  rw [← hWd] at sD hlen
  -- 5: the fix-up
  obtain ⟨ρ0, hρ0⟩ : ∃ s, s = DockW.updS (tmapA x hx) τ1 (fun _ => 0) tout := ⟨_, rfl⟩
  rw [← hρ0] at sD
  have hsh0 : ∀ i, ρ0.sh i = 0 := by rw [hρ0]; exact FinalPass.S5T.updS_sh0 (tmapA x hx) (tmapA_inj x hx) τ1 tout hPD.heads
  have hst0 : ∀ j, ρ0.st (tmapA x hx j) = tout j := fun j => by
    rw [hρ0]; exact FinalPass.S5T.updS_st_in (tmapA x hx) (tmapA_inj x hx) τ1 (fun _ => 0) tout j
  have hout0 : ∀ i, (∀ j, tmapA x hx j ≠ i) → ρ0.st i = τ1.st i := fun i hi => by
    rw [hρ0]; exact FinalPass.S5T.updS_st_out (tmapA x hx) τ1 (fun _ => 0) tout i hi
  obtain ⟨kk, hkk⟩ : ∃ k, k = FinalPass.Seams.symCallOf (callInputs l F kclk coef A a ha) hs ha' Cs carriers :=
    ⟨_, rfl⟩
  have e5 := fix_run x hx cap ρ0 (fun j => hsh0 _) (fun j => PrimT.tabH (PrimT.S3.gatesJ kk j))
    (fun j => PrimT.S3.gatesJ kk j) (fun j => by
      show ρ0.st (tmapA x hx (DataDock.iSym j)) = _ ∨ (ρ0.st (tmapA x hx (DataDock.iSym j)) = [] ∧ _)
      rw [hst0, hkk]
      dsimp only [PrimT.S3.gatesJ, FinalPass.Seams.symCallOf]
      by_cases h : j.val < a'
      · left; rw [dif_pos h]; exact hS j h
      · right; rw [dif_neg h]; exact ⟨hSb j (by omega), rfl⟩)
  -- the machine's run
  have sP := Exec.step (WExec.exec cap (WExec.seq e1 (WExec.seq e2 e3)))
  have sF := Exec.step (WExec.exec cap e5)
  have hne : ∀ i j : Fin 4, i ≠ j → oG x hx i ≠ oG x hx j := fun i j hij e => hij (oG_inj x hx e)
  refine ⟨_, _, ?_, Step.seq (Step.seq sP sD) sF, fun k => ?_, ?_, fun i hi hk => ?_, fun i => ?_, fun q => ?_⟩
  · -- the steps
    have hS1 : c1 ≤ NumsC.CsC l F * X ^ Dsg l F.filterErrDeg :=
      le_trans hc1 (Nat.mul_le_mul_left _ (liftS (by rw [hDsg]; unfold NumsC.DsC; omega)))
    have hS2 : c2 ≤ 4000 * 2 ^ 27 * X ^ Dsg l F.filterErrDeg := by
      have h1 : (fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + n + 2 ≤ 2 * X := by omega
      have h2 : ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + n + 2) ^ 27 ≤ (2 * X) ^ 27 := Nat.pow_le_pow_left h1 27
      have h3 : (2 * X) ^ 27 = 2 ^ 27 * X ^ 27 := mul_pow 2 X 27
      have h4 : X ^ 27 ≤ X ^ Dsg l F.filterErrDeg := liftS (by rw [hDsg]; omega)
      calc c2 ≤ 4000 * ((fpIn l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩).length + n + 2) ^ 27 := hc2
        _ ≤ 4000 * (2 ^ 27 * X ^ 27) := by rw [← h3]; exact Nat.mul_le_mul_left _ h2
        _ ≤ 4000 * (2 ^ 27 * X ^ Dsg l F.filterErrDeg) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
        _ = _ := by ring
    have hS3 : c3 ≤ 100 * (KTZ l F + 30) * X ^ Dsg l F.filterErrDeg := by
      have h1 : n + W + eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + 1 ≤
          (KTZ l F + 30) * X ^ Dg l F.filterErrDeg := by
        have e : (KTZ l F + 30) * X ^ Dg l F.filterErrDeg = KTZ l F * X ^ Dg l F.filterErrDeg +
            30 * X ^ Dg l F.filterErrDeg := by ring
        rw [e]; omega
      have h2 := Nat.mul_le_mul_left (KTZ l F + 30) hGS
      calc c3 ≤ 100 * (n + W + eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + 1) := hc3
        _ ≤ 100 * ((KTZ l F + 30) * X ^ Dg l F.filterErrDeg) := Nat.mul_le_mul_left _ h1
        _ ≤ 100 * ((KTZ l F + 30) * X ^ Dsg l F.filterErrDeg) := Nat.mul_le_mul_left _ h2
        _ = _ := by ring
    have hSd : Data.symCc * (3 * W + 1) ^ Data.symDc ≤ Data.symCc * 82 ^ Data.symDc * X ^ Dsg l F.filterErrDeg := by
      have h0 := Nat.one_le_pow 26 X (by omega)
      have h1 : 3 * W + 1 ≤ 82 * X ^ 26 := by omega
      have h2 : (3 * W + 1) ^ Data.symDc ≤ (82 * X ^ 26) ^ Data.symDc := Nat.pow_le_pow_left h1 _
      have h3 : (82 * X ^ 26) ^ Data.symDc = 82 ^ Data.symDc * X ^ (26 * Data.symDc) := by rw [mul_pow, ← pow_mul]
      have h4 : X ^ (26 * Data.symDc) ≤ X ^ Dsg l F.filterErrDeg := liftS (by rw [hDsg]; omega)
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left _ (le_trans (le_of_le_of_eq h2 h3) (Nat.mul_le_mul_left _ h4))
    have hP : 1 ≤ X ^ Dsg l F.filterErrDeg := Nat.one_le_pow _ _ (by omega)
    have h := costG c1 c2 c3 (Data.symCc * (3 * W + 1) ^ Data.symDc) (X ^ Dsg l F.filterErrDeg)
      (NumsC.CsC l F) (4000 * 2 ^ 27) (100 * (KTZ l F + 30)) (Data.symCc * 82 ^ Data.symDc) hP hS1 hS2 hS3 hSd
    exact h
  · -- the words
    show ((((ρ0.sets (oG x hx 0) _).sets (oG x hx 1) _).sets (oG x hx 2) _).sets (oG x hx 3) _).st (oG x hx k) = _
    rw [swg_word l F kclk coef A a ha ha' Cs carriers translation hcall hs k, ← hkk]
    simp only [WState.sets_st, Function.update_apply, (oG_inj x hx).eq_iff]
    fin_cases k <;> simp
  · -- the request
    have hnI : ∀ j : Fin 4, oG x hx j ≠ sIn x := fun j e => by
      have := congrArg Fin.val e; rw [oG_val] at this; have : (sIn x).val = 150 := rfl; omega
    simp only [WState.sets_st]
    rw [Function.update_of_ne (hnI 3).symm, Function.update_of_ne (hnI 2).symm, Function.update_of_ne (hnI 1).symm,
      Function.update_of_ne (hnI 0).symm]
    have e0 : sIn x = tmapA x hx DataDock.iIN := by unfold tmapA DataDock.nwTmap; rw [if_pos rfl]
    rw [e0, hst0, hinw]
  · -- the residue
    have hk' : ∀ j : Fin 4, i ≠ oG x hx j := fun j => hk j
    simp only [WState.sets_st]
    rw [Function.update_of_ne (hk' 3), Function.update_of_ne (hk' 2), Function.update_of_ne (hk' 1),
      Function.update_of_ne (hk' 0)]
    have hbound : Data.symCc * (3 * W + 1) ^ Data.symDc + 3 * W + n + eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ +
        FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + 2 ≤ Csg l F * X ^ Dsg l F.filterErrDeg := by
      have h0 := Nat.one_le_pow 26 X (by omega)
      have h1 : 3 * W + 1 ≤ 82 * X ^ 26 := by omega
      have h2 : (3 * W + 1) ^ Data.symDc ≤ (82 * X ^ 26) ^ Data.symDc := Nat.pow_le_pow_left h1 _
      have h3 : (82 * X ^ 26) ^ Data.symDc = 82 ^ Data.symDc * X ^ (26 * Data.symDc) := by rw [mul_pow, ← pow_mul]
      have h4 : X ^ (26 * Data.symDc) ≤ X ^ Dsg l F.filterErrDeg := liftS (by rw [hDsg]; omega)
      have hA : Data.symCc * (3 * W + 1) ^ Data.symDc ≤ Data.symCc * 82 ^ Data.symDc * X ^ Dsg l F.filterErrDeg := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (le_trans (le_of_le_of_eq h2 h3) (Nat.mul_le_mul_left _ h4))
      have hB : 3 * W + n + eOf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + FinalPass.Sd.R.Tf l F kclk coef A a ha ⟨⟨n, .sym, a', ha', Cs, carriers, translation⟩, hcall⟩ + 2 ≤
          100 * (KTZ l F + 30) * X ^ Dsg l F.filterErrDeg := by
        have h5 := Nat.mul_le_mul_left (KTZ l F) hGS
        have e : 100 * (KTZ l F + 30) * X ^ Dsg l F.filterErrDeg = 100 * (KTZ l F * X ^ Dsg l F.filterErrDeg) +
            3000 * X ^ Dsg l F.filterErrDeg := by ring
        rw [e]; omega
      have hC : Csg l F * X ^ Dsg l F.filterErrDeg = NumsC.CsC l F * X ^ Dsg l F.filterErrDeg +
          4000 * 2 ^ 27 * X ^ Dsg l F.filterErrDeg + 100 * (KTZ l F + 30) * X ^ Dsg l F.filterErrDeg +
          Data.symCc * 82 ^ Data.symDc * X ^ Dsg l F.filterErrDeg + 100 * X ^ Dsg l F.filterErrDeg := by
        unfold Csg; ring
      rw [hC]; omega
    refine le_trans ?_ hbound
    by_cases hI : ∃ j, tmapA x hx j = i
    · obtain ⟨j, rfl⟩ := hI
      rw [hst0]
      have := hlen j
      omega
    · have hni : ∀ j, tmapA x hx j ≠ i := fun j e => hI ⟨j, e⟩
      rw [hout0 i hni]
      have v0 := tNT_val x hx
      have v1 := tLT_val x hx
      have v2 := tCT_val x hx
      have vD := DT_val
      have hvI : i.val ≠ 150 := fun e => hi (Fin.ext e)
      have h163 : i.val ≠ 163 := fun e => hni (DataDock.iOf Data.sNT) (Fin.ext (by rw [e]; exact v0))
      have h164 : i.val ≠ 164 := fun e => hni (DataDock.iOf Data.sLT) (Fin.ext (by rw [e]; exact v1))
      have h165 : i.val ≠ 165 := fun e => hni (DataDock.iOf Data.sCT) (Fin.ext (by rw [e]; exact v2))
      by_cases hN : i = sNs x hx
      · subst hN; rw [hPD.hSN, List.length_replicate]; omega
      · by_cases hE : i = sEs x hx
        · subst hE; rw [hPD.hSE, List.length_replicate]; omega
        · by_cases hT : i = sTs x hx
          · subst hT; rw [hPD.hST, List.length_replicate]; omega
          · by_cases h1 : i = sk x 1
            · subst h1; rw [hPD.h1]; simp
            · rw [hPD.blank i hvI h163 h164 h165 (fun e => hN (Fin.ext (by rw [e, sNs_val, vD])))
                (fun e => hE (Fin.ext (by rw [e, sEs_val, vD]))) (fun e => hT (Fin.ext (by rw [e, sTs_val, vD])))
                (fun e => h1 (Fin.ext e))]
              simp
  · simp only [WState.sets_sh]; exact hsh0 i
  · simp only [WState.sets_val]; rw [hρ0]; exact hPD.regs q

/-- **SWg** (`SWParts.SWgT l`) on NW's bank `x ≥ DT + 3`. -/
noncomputable def swG : FinalPass.SWParts.SWgT l :=
  ⟨LNS x, LNR, _, fun F => gM x hx l F, sIn x, sOutG x hx,
    fun k e => by
      have := congrArg Fin.val e
      have h1 : (sOutG x hx k).val = 179 + 1789 * k.val := oG_val x hx k
      have h2 : (sIn x).val = 150 := rfl
      omega,
    Kg l, Dg l, Csg l, Dsg l,
    fun F kclk coef A a ha r hm σ hin hsh hbl hv hc => by
      obtain ⟨⟨n, mode, a', ha', Cs, carriers, translation⟩, hcall⟩ := r
      have hm' : mode = .sym := hm
      subst hm'
      exact gRun x hx l F kclk coef A a ha ha' Cs carriers translation hcall σ hin hsh hbl hv hc⟩

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
