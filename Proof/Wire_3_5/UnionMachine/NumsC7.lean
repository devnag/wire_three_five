import Proof.Wire_3_5.UnionMachine.NumsC6
import Proof.Wire_3_5.UnionMachine.NumsPh3

/-! # NW phase (c) over the interface v3: `phC3 x l : NumsPh3.PhC x l`

Phase (c)'s program never writes a stream, so its exit keeps every stream but `sIn` blank, v3's `AfterC`:

* **`cRun`** (the program's run at a request, its exact exit state and the steps' bound, from `cProg_run`,
  `cCost_le`), **`phC3`**.

Paper quantities of the main type: `n`, the mode, `e = n − k`, `T_f` (P3:3044-3048, P3:1188-1189). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsC
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP

section Gate
variable (x : ℕ) (l : Literals)

/-- **(c)'s run at a request**: the exact exit state within `C_s·(|fpIn|+1)^{D_s}` steps. -/
theorem cRun (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (cap : ℕ)
    (hcap : KnC l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DnC l F.filterErrDeg ≤ cap) (σ : St x)
    (hE : Entry x l F kclk coef A a ha r σ) :
    ∃ c, WExec cap (cProg x F.cr (FinalPass.Sd.R.KT l F) (FinalPass.Sd.R.ZT l F)) σ
      (((((σ.seth (sIn x) 0).setv rN r.1.n).setv rM (mOf l F kclk coef A a ha r)).setv rE
        (eOf l F kclk coef A a ha r)).setv rT (FinalPass.Sd.R.Tf l F kclk coef A a ha r)) c ∧
      c ≤ CsC l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsC l F.filterErrDeg := by
  have hX := FinalPass.FpInLen.n_le_fpIn r
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha r).length + 1 := ⟨_, rfl⟩
  rw [← hXd] at hcap ⊢
  have hnX : r.1.n + 1 ≤ X := by omega
  have eZ : DnC l F.filterErrDeg = FinalPass.Sd.R.ZT l F + 2 := rfl
  have eZs : DsC l F.filterErrDeg = FinalPass.Sd.R.ZT l F + 2 := rfl
  rw [eZ] at hcap
  rw [eZs]
  have hKT : 8 ≤ FinalPass.Sd.R.KT l F := by unfold FinalPass.Sd.R.KT; omega
  have hZT : 4 ≤ FinalPass.Sd.R.ZT l F := by unfold FinalPass.Sd.R.ZT; omega
  obtain ⟨Z, hZd⟩ : ∃ v, v = FinalPass.Sd.R.ZT l F := ⟨_, rfl⟩
  obtain ⟨KT, hKTd⟩ : ∃ v, v = FinalPass.Sd.R.KT l F := ⟨_, rfl⟩
  have hP := npow_le r.1.n X (Z + 2) hnX
  have hNZ : (r.1.n + 2) ^ Z ≤ (r.1.n + 2) ^ (Z + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have hN1 : r.1.n + 2 ≤ (r.1.n + 2) ^ (Z + 2) := by
    calc r.1.n + 2 = (r.1.n + 2) ^ 1 := (pow_one _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hneed : (KT + 2 * F.cr + 60) * (r.1.n + 2) ^ (Z + 2) ≤ cap := by
    refine le_trans ?_ hcap
    unfold KnC
    rw [← hZd, ← hKTd, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ hP
  have hTf : FinalPass.Sd.R.Tf l F kclk coef A a ha r ≤ cap := by
    show FinalPass.Sd.R.KT l F * (r.1.n + 2) ^ FinalPass.Sd.R.ZT l F ≤ cap
    rw [← hZd, ← hKTd]
    refine le_trans ?_ hneed
    exact Nat.mul_le_mul (by omega) hNZ
  have hlin : (2 * F.cr + 60) * (r.1.n + 2) ≤ cap := by
    refine le_trans ?_ hneed
    exact Nat.mul_le_mul (by omega) hN1
  obtain ⟨c, hW, hc⟩ := cProg_run l F kclk coef A a ha x cap r σ hE (by nlinarith) hTf (by nlinarith)
  refine ⟨c, hW, hc.trans ?_⟩
  have hk : ((gate0 l F).budget kclk coef A a ha).kOf r.1.n ≤ r.1.n :=
    NumsX.rs_le ((callInputs l F kclk coef A a ha).starParams r.1.n r.2.2.2.2.2.2.1)
  have h1 := cCost_le r.1.n F.cr (((gate0 l F).budget kclk coef A a ha).kOf r.1.n) KT Z hk (by omega)
    (by omega)
  have eTf : FinalPass.Sd.R.Tf l F kclk coef A a ha r = KT * (r.1.n + 2) ^ Z := by rw [hKTd, hZd]; rfl
  rw [eTf, ← hZd, ← hKTd]
  refine h1.trans ?_
  unfold CsC
  rw [← hZd, ← hKTd, Nat.mul_assoc (2000 * _)]
  exact Nat.mul_le_mul_left _ hP

/-- **Phase (c) over the interface v3.** -/
noncomputable def phC3 : NumsPh3.PhC x l where
  s := fun F => (cProg x F.cr (FinalPass.Sd.R.KT l F) (FinalPass.Sd.R.ZT l F)).toProg.size
  M := fun F => (cProg x F.cr (FinalPass.Sd.R.KT l F) (FinalPass.Sd.R.ZT l F)).toProg.compile
  Kn := KnC l
  Dn := DnC l
  Cs := CsC l
  Ds := DsC l
  run := fun F kclk coef A a ha r cap hcap σ hE => by
    obtain ⟨c, hW, hc⟩ := cRun x l F kclk coef A a ha r cap hcap σ hE
    refine ⟨_, c, hc, Exec.step (WExec.exec cap hW), ?_⟩
    have hs0 : ∀ i, σ.sh i = 0 := hE.heads
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hE.hin]
    · intro i hi
      simp [hE.blank i hi]
    · intro i
      simp only [WState.setv_sh, WState.seth_sh, Function.update_apply]
      split_ifs <;> simp [hs0]
    · simp [hE.cell]
    · simp [show rN ≠ rT by decide, show rN ≠ rE by decide, show rN ≠ rM by decide]
    · simp [show rM ≠ rT by decide, show rM ≠ rE by decide]
    · simp [show rE ≠ rT by decide]
    · simp
    · intro q h1 h2 h3 h4
      simp [h1, h2, h3, h4, hE.regs]

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsC
