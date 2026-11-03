import Lean
import Proof.Wire_3_5.UnionMachine.NumsA11
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR12
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsA4
import Proof.Wire_3_5.UnionMachine.NumsA6
import Proof.Wire_3_5.UnionMachine.NumsA9
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Proof.Wire_3_5.UnionMachine.NumsA12Base


noncomputable section
set_option maxRecDepth 120000


/-! # NW phase (a), part 12: the run at a SYM request and `phA3 x hx l : NumsPh3.PhA x l`

Composition of `width_run`, `tapes_run` (the word program `prepW`), `dockPost` (the docked data stage), and
`dockPost`'s unframe, `numsBank`, `fin_run` (the word program `postW`), from (c)'s exit `AfterC` to `AfterV` with
`V = vOf r` in `rV`, within `C_s·X^{D_s}` steps at every capacity `≥ K_n·X^{D_n}` (`X = |fpIn|+1`).

* `sumle`, `mfle`, **`aRun`**, **`phA3`**.

Paper quantity of the main type: `V = |E|·|FlatSeed|·Q` at the SYM requests (P3:3044-3048, 3170-3181). -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.NumsC (g g_ne npow_le)

section Gate
variable (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (l : Literals)

/-- **Phase (a)'s run at a SYM request.** -/
theorem aRun (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (cap : ℕ)
    (hm : r.1.mode = .sym)
    (hcap : Kua l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ Dua l F.filterErrDeg ≤ cap) (σ : St x)
    (hC : NumsPh3.AfterC x l F kclk coef A a ha r σ) :
    ∃ (τ : St x) (n : ℕ), n ≤ CsA l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsA l F.filterErrDeg ∧
      Step (aM x hx l F) n (wenc cap σ).H (wenc cap σ).A (wenc cap τ).H (wenc cap τ).A ∧
      NumsPh3.AfterV x l F kclk coef A a ha r
        (CsA l F * ((fpIn l F kclk coef A a ha r).length + 1) ^ DsA l F.filterErrDeg) τ := by
  -- the numbers
  have hnw : r.1.n ≤ (fpIn l F kclk coef A a ha r).length := FinalPass.FpInLen.n_le_fpIn r
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha r).length + 1 := ⟨_, rfl⟩
  rw [← hXd] at hcap
  rw [← hXd]
  have hX1 : 1 ≤ X := by omega
  have hm0 : mOf l F kclk coef A a ha r = 0 := by simp [mOf, hm]
  have heN : eOf l F kclk coef A a ha r ≤ r.1.n := by unfold eOf; omega
  obtain ⟨Du, hDud⟩ : ∃ v, v = Dua l F.filterErrDeg := ⟨_, rfl⟩
  obtain ⟨U, hUd⟩ : ∃ v, v = X ^ Du := ⟨_, rfl⟩
  have hU1 : 1 ≤ U := by rw [hUd]; exact Nat.one_le_pow _ _ (by omega)
  have lift : ∀ {d : ℕ}, d ≤ Du → X ^ d ≤ U := fun hd => by rw [hUd]; exact Nat.pow_le_pow_right hX1 hd
  have hDu : Du = 3 * D0 l F.filterErrDeg + FinalPass.Sd.R.ZTe l F.filterErrDeg + 27 := by rw [hDud]; rfl
  have hZT : FinalPass.Sd.R.ZT l F = FinalPass.Sd.R.ZTe l F.filterErrDeg := rfl
  have hXU : X ≤ U := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ U := lift (by omega)
  -- the width
  obtain ⟨W, hWd⟩ : ∃ v, v = wOf (fpIn l F kclk coef A a ha r).length r.1.n := ⟨_, rfl⟩
  have hW27 : W ≤ 27 * X ^ 26 := by
    rw [hWd]; unfold wOf
    have h1 : (fpIn l F kclk coef A a ha r).length ≤ X ^ 26 := by
      calc (fpIn l F kclk coef A a ha r).length ≤ X ^ 1 := by rw [pow_one]; omega
        _ ≤ X ^ 26 := Nat.pow_le_pow_right hX1 (by omega)
    have h2 : (r.1.n + 1) ^ 26 ≤ X ^ 26 := Nat.pow_le_pow_left (by omega) 26
    have h3 : 1 ≤ X ^ 26 := Nat.one_le_pow _ _ (by omega)
    omega
  have hWU : W ≤ 27 * U := le_trans hW27 (Nat.mul_le_mul_left _ (lift (by omega)))
  -- `T_f`
  obtain ⟨KTZ, hKTZ⟩ : ∃ v, v = FinalPass.Sd.R.KT l F * 2 ^ FinalPass.Sd.R.ZT l F := ⟨_, rfl⟩
  have hTU : FinalPass.Sd.R.Tf l F kclk coef A a ha r ≤ KTZ * U := by
    show FinalPass.Sd.R.KT l F * (r.1.n + 2) ^ FinalPass.Sd.R.ZT l F ≤ KTZ * U
    have h1 := npow_le r.1.n X (FinalPass.Sd.R.ZT l F) (by omega)
    have h2 : X ^ FinalPass.Sd.R.ZT l F ≤ U := lift (by rw [hZT]; omega)
    rw [hKTZ, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_trans h1 (Nat.mul_le_mul_left _ h2))
  -- the numbers front's capacity and the rewind bound
  obtain ⟨cap₀, hc0d⟩ : ∃ v, v = K0 l F * X ^ D0 l F.filterErrDeg := ⟨_, rfl⟩
  have hc0U : cap₀ ≤ K0 l F * U := by rw [hc0d]; exact Nat.mul_le_mul_left _ (lift (by omega))
  obtain ⟨Bh, hBhd⟩ : ∃ v, v = K1a l F * X ^ D3a l F.filterErrDeg := ⟨_, rfl⟩
  have hBhU : Bh ≤ K1a l F * U := by rw [hBhd]; exact Nat.mul_le_mul_left _ (lift (by unfold D3a; omega))
  have hcube : 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) ≤ Bh := by
    have h1 : cap₀ + 2 ≤ (K0 l F + 2) * X ^ D0 l F.filterErrDeg := by
      have := Nat.one_le_pow (D0 l F.filterErrDeg) X (by omega)
      rw [hc0d]; nlinarith
    have h2 : (cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2) ≤ (K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg := by
      calc (cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2) = (cap₀ + 2) ^ 3 := by ring
        _ ≤ ((K0 l F + 2) * X ^ D0 l F.filterErrDeg) ^ 3 := Nat.pow_le_pow_left h1 3
        _ = (K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg := by unfold D3a; rw [mul_pow, ← pow_mul]; ring_nf
    rw [hBhd]; unfold K1a
    calc 3000000 * ((cap₀ + 2) * (cap₀ + 2) * (cap₀ + 2)) ≤ 3000000 * ((K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg) :=
          Nat.mul_le_mul_left _ h2
      _ = 3000000 * (K0 l F + 2) ^ 3 * X ^ D3a l F.filterErrDeg := by ring
  -- the capacity's needs
  have hKu : Kua l F * U = (2 * K0 l F + K1a l F + KTZ + 3 * D0 l F.filterErrDeg + 1000) * U := by
    unfold Kua; rw [hKTZ]
  have hcapU : (2 * K0 l F + K1a l F + KTZ + 3 * D0 l F.filterErrDeg + 1000) * U ≤ cap := by
    rw [← hKu, hUd, hDud]; exact hcap
  have hVbound : ∀ V : ℕ, V ≤ cap₀ * (fpIn l F kclk coef A a ha r).length → V ≤ K0 l F * U := by
    intro V hV
    refine le_trans hV ?_
    rw [hc0d, Nat.mul_assoc]
    refine Nat.mul_le_mul_left _ ?_
    calc X ^ D0 l F.filterErrDeg * (fpIn l F kclk coef A a ha r).length ≤ X ^ D0 l F.filterErrDeg * X :=
          Nat.mul_le_mul_left _ (by omega)
      _ = X ^ (D0 l F.filterErrDeg + 1) := (pow_succ _ _).symm
      _ ≤ U := lift (by omega)
  have hc0cap : cap₀ ≤ cap := by
    refine le_trans hc0U (le_trans (Nat.mul_le_mul_right U (by omega :
      K0 l F ≤ 2 * K0 l F + K1a l F + KTZ + 3 * D0 l F.filterErrDeg + 1000)) hcapU)
  obtain ⟨hcW, hcT, hcD, -, -⟩ := capA U (K0 l F) (K1a l F) KTZ (D0 l F.filterErrDeg) cap₀ 0 Bh
    (FinalPass.Sd.R.Tf l F kclk coef A a ha r) W r.1.n (eOf l F kclk coef A a ha r)
    (fpIn l F kclk coef A a ha r).length cap hc0U (Nat.zero_le _) hBhU hTU hWU (by omega) (by omega) (by omega) hU1
    hcapU
  -- 1: the width
  obtain ⟨cw, ew, hcw⟩ := width_run x cap (fpIn l F kclk coef A a ha r) r.1.n σ hC.hin (hC.heads _) hC.hn
    (fun j => hC.regs _ (g_ne j).1 (g_ne j).2.1 (g_ne j).2.2.1 (g_ne j).2.2.2) (by rw [← hWd]; omega)
  rw [← hWd] at ew
  -- 2: the data stage's inputs, the stash
  obtain ⟨τ1, ct, et, hPD, hct⟩ := tapes_run x hx cap (fpIn l F kclk coef A a ha r) r.1.n W
    (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r) (σ.setv (g 2) W)
    (by rw [WState.setv_st]; exact hC.hin) (fun i hi => by rw [WState.setv_st]; exact hC.clean i hi)
    (fun i => by rw [WState.setv_sh]; exact hC.heads i) (by rw [WState.setv_cell]; exact hC.cell)
    (by rw [WState.setv_val, Function.update_of_ne (show rN ≠ g 2 by decide)]; exact hC.hn)
    (by rw [WState.setv_val, Function.update_self])
    (by rw [WState.setv_val, Function.update_of_ne (show rE ≠ g 2 by decide)]; exact hC.he)
    (by rw [WState.setv_val, Function.update_of_ne (show rT ≠ g 2 by decide)]; exact hC.ht)
    (fun q a1 a2 a3 a4 => by
      rw [WState.setv_val, Function.update_of_ne a4]
      by_cases hq : q = rM
      · subst hq; rw [hC.hm, hm0]
      · exact hC.regs q a1 hq a2 a3)
    hcT
  rw [hWd] at hPD
  -- 3: the data stage, the counts onto stream `113`
  obtain ⟨tout, ρ, cu, sD, eu, hNI, hSN, hSE, hST, hW0, hW1, hres, hcu⟩ := dockPost l F kclk coef A a ha x hx r hm
    cap (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r) τ1 hPD (by rw [← hWd]; omega)
  rw [← hWd] at sD hres hcu
  -- 4: the SYM numbers
  obtain ⟨ω', cn, h, en, hst, hsh', hhc, hcell, hV, hGF, hQ, hval, hcn⟩ := numsBank l F kclk coef A a ha x r hm cap₀
    cap (by rw [hc0d, hXd]) hc0cap ρ hNI
  have hVle : vOf l F kclk coef A a ha r ≤ K0 l F * U := by
    apply hVbound
    rw [← hV]
    exact Nat.mul_le_mul hGF hQ
  obtain ⟨-, -, -, -, hcF⟩ := capA U (K0 l F) (K1a l F) KTZ (D0 l F.filterErrDeg) cap₀ (vOf l F kclk coef A a ha r)
    Bh (FinalPass.Sd.R.Tf l F kclk coef A a ha r) W r.1.n (eOf l F kclk coef A a ha r)
    (fpIn l F kclk coef A a ha r).length cap hc0U hVle hBhU hTU hWU (by omega) (by omega) (by omega) hU1 hcapU
  -- 5: the finish
  obtain ⟨cf, ef, hcf⟩ := fin_run x hx cap cap₀ (K1a l F) (D3a l F.filterErrDeg) h (fpIn l F kclk coef A a ha r)
    r.1.n (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r) (vOf l F kclk coef A a ha r) ω'
    (by rw [hst]; exact hNI.hin) (by rw [hst]; exact hSN) (by rw [hst]; exact hSE) (by rw [hst]; exact hST)
    (fun i hi => by rw [hsh', Function.update_of_ne hi]; exact hNI.heads i)
    (by rw [hsh', Function.update_self]) (by rw [← hXd, ← hBhd]; omega) hval hV hGF hQ
    (by rw [← hXd, ← hBhd]; omega)
  -- the steps' atoms
  have hKu1 : 1 ≤ Kua l F := by unfold Kua; omega
  have hK1K : K1a l F ≤ Kua l F := by unfold Kua; omega
  have hKK3 : Kua l F ≤ Kua l F ^ 3 := Nat.le_self_pow (by norm_num) _
  have hUU3 : U ≤ U ^ 3 := Nat.le_self_pow (by norm_num) _
  have hDsA : DsA l F.filterErrDeg = 3 * Du + 26 * Data.symDc := by unfold DsA; rw [hDud]
  have hUX : U ≤ X ^ DsA l F.filterErrDeg := by rw [hUd]; exact Nat.pow_le_pow_right hX1 (by rw [hDsA]; omega)
  have hU3X : U ^ 3 ≤ X ^ DsA l F.filterErrDeg := by
    rw [hUd, ← pow_mul]; exact Nat.pow_le_pow_right hX1 (by rw [hDsA]; omega)
  have hZX : X ^ (26 * Data.symDc) ≤ X ^ DsA l F.filterErrDeg := Nat.pow_le_pow_right hX1 (by rw [hDsA]; omega)
  have hKuU : Kua l F * U ≤ Kua l F ^ 3 * U ^ 3 := Nat.mul_le_mul hKK3 hUU3
  have hK1U : K1a l F * U ≤ Kua l F ^ 3 * U ^ 3 := Nat.mul_le_mul (le_trans hK1K hKK3) hUU3
  have hKuP : Kua l F ^ 3 * U ^ 3 ≤ Kua l F ^ 3 * X ^ DsA l F.filterErrDeg := Nat.mul_le_mul_left _ hU3X
  have hcw2 : cw ≤ 4000 * 2 ^ 27 * U := by
    have h1 : (fpIn l F kclk coef A a ha r).length + r.1.n + 2 ≤ 2 * X := by omega
    have h2 : ((fpIn l F kclk coef A a ha r).length + r.1.n + 2) ^ 27 ≤ (2 * X) ^ 27 := Nat.pow_le_pow_left h1 27
    have h3 : (2 * X) ^ 27 = 2 ^ 27 * X ^ 27 := mul_pow 2 X 27
    have h4 : X ^ 27 ≤ U := lift (by omega)
    calc cw ≤ 4000 * ((fpIn l F kclk coef A a ha r).length + r.1.n + 2) ^ 27 := hcw
      _ ≤ 4000 * (2 ^ 27 * X ^ 27) := by rw [← h3]; exact Nat.mul_le_mul_left _ h2
      _ ≤ 4000 * (2 ^ 27 * U) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h4)
      _ = 4000 * 2 ^ 27 * U := by ring
  have hs := sumle U (K0 l F) (K1a l F) KTZ (D0 l F.filterErrDeg) r.1.n W (eOf l F kclk coef A a ha r)
    (FinalPass.Sd.R.Tf l F kclk coef A a ha r) hU1 (by omega) hWU (by omega) hTU
  rw [← hKu] at hs
  have hct2 : ct ≤ 100 * (Kua l F * U) := by omega
  have hfd : Data.symCc * (3 * W + 1) ^ Data.symDc ≤ Data.symCc * 82 ^ Data.symDc * X ^ (26 * Data.symDc) := by
    have h0 := Nat.one_le_pow 26 X (by omega)
    have h1 : 3 * W + 1 ≤ 82 * X ^ 26 := by omega
    have h2 : (3 * W + 1) ^ Data.symDc ≤ (82 * X ^ 26) ^ Data.symDc := Nat.pow_le_pow_left h1 _
    have h3 : (82 * X ^ 26) ^ Data.symDc = 82 ^ Data.symDc * X ^ (26 * Data.symDc) := by rw [mul_pow, ← pow_mul]
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (le_of_le_of_eq h2 h3)
  have hcu2 : cu ≤ 1100 * U := by omega
  have hcn2 : cn ≤ K1a l F * U := le_trans hcn (le_trans hcube hBhU)
  have hcf2 : cf ≤ 5000 * (27 * (Kua l F ^ 3 * U ^ 3)) := by
    have hMf := mfle U (K0 l F) (K1a l F) KTZ (D0 l F.filterErrDeg) (D3a l F.filterErrDeg) cap₀
      (vOf l F kclk coef A a ha r) Bh r.1.n (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r)
      (fpIn l F kclk coef A a ha r).length hU1 hc0U hVle hBhU hTU (by omega) (by omega) (by omega)
      (by unfold D3a; omega)
    rw [← hKu] at hMf
    have hcf' := hcf
    rw [← hXd, ← hBhd] at hcf'
    have h3 := Nat.pow_le_pow_left hMf 3
    have h4 : (3 * (Kua l F * U)) ^ 3 = 27 * (Kua l F ^ 3 * U ^ 3) := by ring
    rw [h4] at h3
    exact le_trans hcf' (Nat.mul_le_mul_left _ h3)
  have hres2 : Data.symCc * (3 * W + 1) ^ Data.symDc + 3 * W + r.1.n + eOf l F kclk coef A a ha r +
      FinalPass.Sd.R.Tf l F kclk coef A a ha r + 2 ≤ CsA l F * X ^ DsA l F.filterErrDeg := by
    have e1 : CsA l F * X ^ DsA l F.filterErrDeg = 10 ^ 12 * X ^ DsA l F.filterErrDeg +
        200000 * (Kua l F ^ 3 * X ^ DsA l F.filterErrDeg) +
        Data.symCc * 82 ^ Data.symDc * X ^ DsA l F.filterErrDeg := by unfold CsA; ring
    have hA : Kua l F * U ≤ Kua l F ^ 3 * X ^ DsA l F.filterErrDeg := le_trans hKuU hKuP
    have hB : Data.symCc * (3 * W + 1) ^ Data.symDc ≤ Data.symCc * 82 ^ Data.symDc * X ^ DsA l F.filterErrDeg :=
      le_trans hfd (Nat.mul_le_mul_left _ hZX)
    rw [e1]
    linarith
  -- the registers after (a)
  have f1 : fval r.1.n (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r)
      (vOf l F kclk coef A a ha r) rN = r.1.n := by unfold fval; rw [if_pos rfl]
  have f2 : fval r.1.n (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r)
      (vOf l F kclk coef A a ha r) rM = mOf l F kclk coef A a ha r := by
    rw [hm0]; unfold fval
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  have f3 : fval r.1.n (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r)
      (vOf l F kclk coef A a ha r) rE = eOf l F kclk coef A a ha r := by
    unfold fval; rw [if_neg (by decide), if_pos rfl]
  have f4 : fval r.1.n (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r)
      (vOf l F kclk coef A a ha r) rT = FinalPass.Sd.R.Tf l F kclk coef A a ha r := by
    unfold fval; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
  have f5 : fval r.1.n (eOf l F kclk coef A a ha r) (FinalPass.Sd.R.Tf l F kclk coef A a ha r)
      (vOf l F kclk coef A a ha r) rV = vOf l F kclk coef A a ha r := by
    unfold fval; rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
  have f6 : ∀ q, q ≠ rN → q ≠ rM → q ≠ rE → q ≠ rT → q ≠ rV → fval r.1.n (eOf l F kclk coef A a ha r)
      (FinalPass.Sd.R.Tf l F kclk coef A a ha r) (vOf l F kclk coef A a ha r) q = 0 := by
    intro q a1 _ a3 a4 a5; unfold fval; rw [if_neg a1, if_neg a3, if_neg a4, if_neg a5]
  -- the machine's run
  have sP := Exec.step (WExec.exec cap (WExec.seq ew et))
  have sQ := Exec.step (WExec.exec cap (WExec.seq eu (WExec.seq en ef)))
  refine ⟨_, _, ?_, Step.seq (Step.seq sP sD) sQ, ?_⟩
  · have hfin := costA U (X ^ DsA l F.filterErrDeg) (X ^ (26 * Data.symDc)) (Kua l F) (Data.symCc * 82 ^ Data.symDc)
      cw ct (Data.symCc * (3 * W + 1) ^ Data.symDc) cu cn cf (Kua l F * U) (K1a l F * U) (Kua l F ^ 3 * U ^ 3) hU1 hUX
      hcw2 hct2 hfd hcu2 hcn2 hcf2 hKuU hK1U (Nat.mul_le_mul_left _ hZX) hKuP
    unfold CsA
    exact hfin
  · refine ⟨?_, ?_, ?_, fun _ => rfl, ?_, fun i h0 _ _ => ?_, ?_, ?_, ?_, ?_, ?_, fun q a1 a2 a3 a4 a5 => ?_⟩
    · show ω'.st (sIn x) = _; rw [hst]; exact hNI.hin
    · show ω'.st (sW0 x) = []; rw [hst]; exact hW0
    · show ω'.st (sW1 x) = []; rw [hst]; exact hW1
    · show ω'.cell = false; exact hcell
    · show (ω'.st i).length ≤ _; rw [hst]; exact le_trans (hres i h0) hres2
    · exact f1
    · exact f2
    · exact f3
    · exact f4
    · exact f5
    · exact f6 q a1 a2 a3 a4 a5

/-- **Phase (a) over the interface v3** (on NW's bank `x ≥ DT + 3`). -/
noncomputable def phA3 : NumsPh3.PhA x l :=
  ⟨_, fun F => aM x hx l F, Kua l, Dua l, CsA l, DsA l,
    fun F kclk coef A a ha r cap hm hcap σ hC => aRun x hx l F kclk coef A a ha r cap hm hcap σ hC⟩

end Gate

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
