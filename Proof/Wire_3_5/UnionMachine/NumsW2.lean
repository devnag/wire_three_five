import Lean
import Proof.Wire_3_5.UnionMachine.NumsW1
import Proof.Wire_3_5.UnionMachine.NumsPh4
import Proof.Wire_3_5.UnionMachine.NumsA12
import Proof.Wire_3_5.UnionMachine.NumsC7
import Proof.Wire_3_5.FinalPass.Core8
import Statement_Wire_3_5
import Proof.Wire_3_5.FinalPass.CoreIfaceMJ
import Proof.Wire_3_5.FinalPass.FpInLen
import Proof.Wire_3_5.FinalPass.PlanFP
import Proof.Wire_3_5.FinalPass.SdR12
import Proof.Wire_3_5.FinalPass.SdR2
import Proof.Wire_3_5.FinalPass.Seams
import Proof.Wire_3_5.Assembly.Gate0
import Proof.Wire_3_5.Primitive.Writers.Plan
import Proof.Wire_3_5.Assembly.Split
import Proof.Wire_3_5.UnionMachine.NumsPh2
import Proof.Wire_3_5.UnionMachine.NumsPh3
import Proof.Wire_3_5.UnionMachine.NumsW2Base


noncomputable section
set_option maxRecDepth 120000


/-! # NW assembly: `numsOfPhases' x l : NumsPh4.NumsOfPhases' x l`, and `nwOf`

P3:3044-3048, 3170-3181: the numbers S4 starts from, `frame (binary T_f 0)` and `frame (binary T_f Den)`, from the four
phases on NW's bank (`WState (LNS x) LNR`):

1. (c): `n`, the mode bit, `e`, `T_f` (`AfterC`);
2. the branch on the mode bit `rM` (`iteMachine (rTape rM)`): (b) at THR, (a) at SYM (`AfterV`: `V` in `rV`);
3. `clrW`: `rN := 0`, `rM := 0` (#270: (d) needs every register but `rT`, `rE`, `rV` zero);
4. (d) v4 (`PhD'`): `Final` at `T = T_f`, `max(2^e·V, 1) = Den` (`denSplit`), fitting `T_f` bits (`fpDen_ltR`),
   below the capacity `T + e + V + 2` (`vOf_le`: `V ≤ K_V·X^{D_V}`).

The capacity `K_c·X^{D_k}` dominates every phase's; steps and residue `C_s·X^{D_s}`; the exponents are functions of
`fe` alone. **The bank width**: (a) needs `x ≥ DT + 3` (`phA3`), the (b) needs `x ≥ dX(TW l, NW l)`; the assembly is
generic in `x`, and `nwOf` takes `x` with `DT + 3 ≤ x` (the chosen `x = max(DT + 3, dX(TW l, NW l))` is a function of
`l`, `xNW`).

* `nwIteT`, `nwIteF`, `clrW`, `clr_run`, `nwM`, `KTZ`, `nwKc`, `nwDk`, `nwE`, `nwCs`, `nwDs`, `nw_bound`, **`nwRun`**,
  **`numsOfPhases'`**, `xNW`, **`nwOf`**.

Paper quantity of the main type: the final pass's denominator `Den` in `T_f`-bit binary. -/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.NumsA
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.UnionMachine.NumsPh2
open NearCubicWires.WireExponent3_5.FinalPass.PlanFP NearCubicWires.WireExponent3_5.Split
open NearCubicWires.WireExponent3_5.PrimAsm.Plan NearCubicWires.WireExponent3_5.FinalPass.Finish
open NearCubicWires.RepairOrdinary.SignedSortKey (binary)
open NearCubicWires.WireExponent3_5.FinalPass.Seams (fpDen)

section Asm
variable (x : ℕ) (l : Literals) (pc : NumsPh3.PhC x l) (pa : NumsPh3.PhA x l) (pb : NumsPh3.PhB x l)
  (pd : NumsPh4.PhD' x)

/-- **NW's machine at a gate**: (c) ; the branch (b)/(a) on `rM` ; `clrW` ; (d). -/
noncomputable def nwM (F : GateFree l) :=
  Composition.machine (Composition.machine (Composition.machine (pc.M F)
    (iteMachine (rTape (ns := LNS x) (nr := LNR) rM) (pb.M F) (pa.M F))) (clrW x).toProg.compile) pd.M

/-- `T_f`'s coefficient with the `2^{Z_T}` of `(n+2)^{Z_T} ≤ 2^{Z_T}X^{Z_T}`. -/
noncomputable def KTZ (F : GateFree l) : ℕ := FinalPass.Sd.R.KT l F * 2 ^ FinalPass.Sd.R.ZT l F

/-- The capacity's coefficient and degree. -/
noncomputable def nwKc (F : GateFree l) : ℕ := pc.Kn F + pa.Kn F + pb.Kn F + KTZ l F + KV l F + 10
noncomputable def nwDk (fe : ℕ) : ℕ := pc.Dn fe + pa.Dn fe + pb.Dn fe + FinalPass.Sd.R.ZTe l fe + DV l fe + 1

/-- (d)'s argument's degree, and the steps' coefficient and degree. -/
noncomputable def nwE (fe : ℕ) : ℕ := FinalPass.Sd.R.ZTe l fe + DV l fe
noncomputable def nwCs (F : GateFree l) : ℕ := pc.Cs F + pa.Cs F + pb.Cs F + pd.C * (KTZ l F + KV l F + 2) ^ pd.D + 20
noncomputable def nwDs (fe : ℕ) : ℕ := pc.Ds fe + pa.Ds fe + pb.Ds fe + nwE l fe * pd.D + 1

end Asm

section Run
variable (x : ℕ) (l : Literals) (pc : NumsPh3.PhC x l) (pa : NumsPh3.PhA x l) (pb : NumsPh3.PhB x l)
  (pd : NumsPh4.PhD' x)

/-- **NW's run at a request of the family**: `CoreWordsMJ.run`'s conclusion for `nwM`. -/
theorem nwRun (F : GateFree l) (kclk coef A a : ℕ) (ha : a ≤ kclk + 1) (r : FReq l F kclk coef A a ha) (σ : St x)
    (hin : σ.st (sIn x) = frame (fpIn l F kclk coef A a ha r)) (hsh : ∀ i, σ.sh i = 0)
    (hbl : ∀ i, i ≠ sIn x → σ.st i = []) (hv : ∀ q, σ.val q = 0) (hcell : σ.cell = false) :
    ∃ (τ : St x) (n : ℕ), n ≤ nwCs x l pc pa pb pd F * ((fpIn l F kclk coef A a ha r).length + 1) ^ nwDs x l pc pa pb pd F.filterErrDeg ∧
      Step (nwM x l pc pa pb pd F) n
        (wenc (nwKc x l pc pa pb F * ((fpIn l F kclk coef A a ha r).length + 1) ^ nwDk x l pc pa pb F.filterErrDeg) σ).H
        (wenc (nwKc x l pc pa pb F * ((fpIn l F kclk coef A a ha r).length + 1) ^ nwDk x l pc pa pb F.filterErrDeg) σ).A
        (wenc (nwKc x l pc pa pb F * ((fpIn l F kclk coef A a ha r).length + 1) ^ nwDk x l pc pa pb F.filterErrDeg) τ).H
        (wenc (nwKc x l pc pa pb F * ((fpIn l F kclk coef A a ha r).length + 1) ^ nwDk x l pc pa pb F.filterErrDeg) τ).A ∧
      (∀ k : Fin 2, τ.st (sOutN x k) = frame (binary (FinalPass.Sd.R.Tf l F kclk coef A a ha r)
        ((![0, fpDen l F kclk coef A a ha r] : Fin 2 → ℕ) k))) ∧
      τ.st (sIn x) = frame (fpIn l F kclk coef A a ha r) ∧
      (∀ i, i ≠ sIn x → (∀ k, i ≠ sOutN x k) →
        (τ.st i).length ≤ nwCs x l pc pa pb pd F * ((fpIn l F kclk coef A a ha r).length + 1) ^ nwDs x l pc pa pb pd F.filterErrDeg) ∧
      (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  have hnw : r.1.n ≤ (fpIn l F kclk coef A a ha r).length := FinalPass.FpInLen.n_le_fpIn r
  obtain ⟨X, hXd⟩ : ∃ v, v = (fpIn l F kclk coef A a ha r).length + 1 := ⟨_, rfl⟩
  rw [← hXd]
  have hX1 : 1 ≤ X := by omega
  have hnX : r.1.n + 1 ≤ X := by omega
  obtain ⟨cap, hcapd⟩ : ∃ v, v = nwKc x l pc pa pb F * X ^ nwDk x l pc pa pb F.filterErrDeg := ⟨_, rfl⟩
  rw [← hcapd]
  have hDk : nwDk x l pc pa pb F.filterErrDeg = pc.Dn F.filterErrDeg + pa.Dn F.filterErrDeg + pb.Dn F.filterErrDeg +
      FinalPass.Sd.R.ZTe l F.filterErrDeg + DV l F.filterErrDeg + 1 := rfl
  have hKc : nwKc x l pc pa pb F = pc.Kn F + pa.Kn F + pb.Kn F + KTZ l F + KV l F + 10 := rfl
  have hDs : nwDs x l pc pa pb pd F.filterErrDeg = pc.Ds F.filterErrDeg + pa.Ds F.filterErrDeg +
      pb.Ds F.filterErrDeg + nwE l F.filterErrDeg * pd.D + 1 := rfl
  have hE : nwE l F.filterErrDeg = FinalPass.Sd.R.ZTe l F.filterErrDeg + DV l F.filterErrDeg := rfl
  have liftK : ∀ {d : ℕ}, d ≤ nwDk x l pc pa pb F.filterErrDeg → X ^ d ≤ X ^ nwDk x l pc pa pb F.filterErrDeg :=
    fun hd => Nat.pow_le_pow_right hX1 hd
  have liftS : ∀ {d : ℕ}, d ≤ nwDs x l pc pa pb pd F.filterErrDeg →
      X ^ d ≤ X ^ nwDs x l pc pa pb pd F.filterErrDeg := fun hd => Nat.pow_le_pow_right hX1 hd
  have capc : pc.Kn F * X ^ pc.Dn F.filterErrDeg ≤ cap := by
    rw [hcapd]; exact Nat.mul_le_mul (by rw [hKc]; omega) (liftK (by rw [hDk]; omega))
  have capa : pa.Kn F * X ^ pa.Dn F.filterErrDeg ≤ cap := by
    rw [hcapd]; exact Nat.mul_le_mul (by rw [hKc]; omega) (liftK (by rw [hDk]; omega))
  have capb : pb.Kn F * X ^ pb.Dn F.filterErrDeg ≤ cap := by
    rw [hcapd]; exact Nat.mul_le_mul (by rw [hKc]; omega) (liftK (by rw [hDk]; omega))
  -- (d)'s numbers
  have hZT : FinalPass.Sd.R.ZT l F = FinalPass.Sd.R.ZTe l F.filterErrDeg := rfl
  have hTX : FinalPass.Sd.R.Tf l F kclk coef A a ha r ≤ KTZ l F * X ^ nwE l F.filterErrDeg := by
    show FinalPass.Sd.R.KT l F * (r.1.n + 2) ^ FinalPass.Sd.R.ZT l F ≤ _
    have h1 := NumsC.npow_le r.1.n X (FinalPass.Sd.R.ZT l F) hnX
    have h2 : X ^ FinalPass.Sd.R.ZT l F ≤ X ^ nwE l F.filterErrDeg :=
      Nat.pow_le_pow_right hX1 (by rw [hZT, hE]; omega)
    unfold KTZ; rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (le_trans h1 (Nat.mul_le_mul_left _ h2))
  have hVX : vOf l F kclk coef A a ha r ≤ KV l F * X ^ nwE l F.filterErrDeg := by
    have h1 := vOf_le l F kclk coef A a ha r
    rw [← hXd] at h1
    exact le_trans h1 (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX1 (by rw [hE]; omega)))
  have heN : eOf l F kclk coef A a ha r ≤ r.1.n := by unfold eOf; omega
  have hXE : X ≤ X ^ nwE l F.filterErrDeg := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ _ := Nat.pow_le_pow_right hX1 (by rw [hE]; unfold DV; omega)
  have hEk : X ^ nwE l F.filterErrDeg ≤ X ^ nwDk x l pc pa pb F.filterErrDeg := liftK (by rw [hDk, hE]; omega)
  have hk1 : 1 ≤ X ^ nwDk x l pc pa pb F.filterErrDeg := Nat.one_le_pow _ _ (by omega)
  have capd : FinalPass.Sd.R.Tf l F kclk coef A a ha r + eOf l F kclk coef A a ha r + vOf l F kclk coef A a ha r + 2
      ≤ cap := by
    rw [hcapd, hKc]
    have a1 : KTZ l F * X ^ nwE l F.filterErrDeg ≤ KTZ l F * X ^ nwDk x l pc pa pb F.filterErrDeg :=
      Nat.mul_le_mul_left _ hEk
    have a2 : KV l F * X ^ nwE l F.filterErrDeg ≤ KV l F * X ^ nwDk x l pc pa pb F.filterErrDeg :=
      Nat.mul_le_mul_left _ hEk
    have e1 : (pc.Kn F + pa.Kn F + pb.Kn F + KTZ l F + KV l F + 10) * X ^ nwDk x l pc pa pb F.filterErrDeg =
        pc.Kn F * X ^ nwDk x l pc pa pb F.filterErrDeg + pa.Kn F * X ^ nwDk x l pc pa pb F.filterErrDeg +
        pb.Kn F * X ^ nwDk x l pc pa pb F.filterErrDeg + KTZ l F * X ^ nwDk x l pc pa pb F.filterErrDeg +
        KV l F * X ^ nwDk x l pc pa pb F.filterErrDeg + 10 * X ^ nwDk x l pc pa pb F.filterErrDeg := by ring
    rw [e1]; omega
  have hXcap : X ≤ cap := by
    rw [hcapd]
    exact le_trans (le_trans hXE hEk) (Nat.le_mul_of_pos_left _ (by rw [hKc]; omega))
  -- 1: (c)
  obtain ⟨τc, nc, hnc, sc, hC⟩ := pc.run F kclk coef A a ha r cap (by rw [← hXd]; exact capc) σ
    ⟨hin, hsh, hbl, hv, hcell⟩
  rw [← hXd] at hnc
  -- 2: the branch on the mode bit
  have hbit := wbit_r cap τc rM
  rw [hC.hm] at hbit
  obtain ⟨τab, nab, B, hB, hnab, sab, hAV⟩ : ∃ (τ : St x) (n B : ℕ),
      B ≤ (pa.Cs F + pb.Cs F) * X ^ nwDs x l pc pa pb pd F.filterErrDeg ∧
      n ≤ (pa.Cs F + pb.Cs F) * X ^ nwDs x l pc pa pb pd F.filterErrDeg ∧
      Step (iteMachine (rTape (ns := LNS x) (nr := LNR) rM) (pb.M F) (pa.M F)) (n + 1) (wenc cap τc).H
        (wenc cap τc).A (wenc cap τ).H (wenc cap τ).A ∧
      NumsPh3.AfterV x l F kclk coef A a ha r B τ := by
    cases hmode : r.1.mode with
    | thr =>
      obtain ⟨τ, n, hn, s, hA⟩ := pb.run F kclk coef A a ha r cap hmode (by rw [← hXd]; exact capb) τc hC
      rw [← hXd] at hn hA
      have hm1 : mOf l F kclk coef A a ha r = 1 := by simp [mOf, hmode]
      have hb : (wenc cap τc).bit (rTape (ns := LNS x) (nr := LNR) rM) = true := by rw [hbit, hm1]; decide
      refine ⟨τ, n, _, ?_, ?_, nwIteT (rTape (ns := LNS x) (nr := LNR) rM) (pb.M F) (pa.M F) (wenc cap τc)
        (wenc cap τ) n hb s, hA⟩
      · exact Nat.mul_le_mul (by omega) (liftS (by rw [hDs]; omega))
      · exact le_trans hn (Nat.mul_le_mul (by omega) (liftS (by rw [hDs]; omega)))
    | sym =>
      obtain ⟨τ, n, hn, s, hA⟩ := pa.run F kclk coef A a ha r cap hmode (by rw [← hXd]; exact capa) τc hC
      rw [← hXd] at hn hA
      have hm0 : mOf l F kclk coef A a ha r = 0 := by simp [mOf, hmode]
      have hb : (wenc cap τc).bit (rTape (ns := LNS x) (nr := LNR) rM) = false := by rw [hbit, hm0]; decide
      refine ⟨τ, n, _, ?_, ?_, nwIteF (rTape (ns := LNS x) (nr := LNR) rM) (pb.M F) (pa.M F) (wenc cap τc)
        (wenc cap τ) n hb s, hA⟩
      · exact Nat.mul_le_mul (by omega) (liftS (by rw [hDs]; omega))
      · exact le_trans hn (Nat.mul_le_mul (by omega) (liftS (by rw [hDs]; omega)))
  -- 3: `rN := 0`, `rM := 0`
  have hmle : mOf l F kclk coef A a ha r ≤ 1 := by unfold mOf; split <;> omega
  have ecl := clr_run x cap τab r.1.n (mOf l F kclk coef A a ha r) hAV.hn hAV.hm (by omega) (by omega)
  have sclr := Exec.step (WExec.exec cap ecl)
  -- 4: (d)
  have hDB : NumsPh3.DBank x ((τab.setv rN 0).setv rM 0) (frame (fpIn l F kclk coef A a ha r))
      (FinalPass.Sd.R.Tf l F kclk coef A a ha r) (eOf l F kclk coef A a ha r) (vOf l F kclk coef A a ha r) B :=
    ⟨by simp only [WState.setv_st]; exact hAV.hin, by simp only [WState.setv_st]; exact hAV.hw0,
      by simp only [WState.setv_st]; exact hAV.hw1, fun i => by simp only [WState.setv_sh]; exact hAV.heads i,
      by simp only [WState.setv_cell]; exact hAV.cell,
      fun i a1 a2 a3 => by simp only [WState.setv_st]; exact hAV.resid i a1 a2 a3,
      by rw [WState.setv_val, Function.update_of_ne (show rT ≠ rM by decide), WState.setv_val,
        Function.update_of_ne (show rT ≠ rN by decide)]; exact hAV.ht,
      by rw [WState.setv_val, Function.update_of_ne (show rE ≠ rM by decide), WState.setv_val,
        Function.update_of_ne (show rE ≠ rN by decide)]; exact hAV.he,
      by rw [WState.setv_val, Function.update_of_ne (show rV ≠ rM by decide), WState.setv_val,
        Function.update_of_ne (show rV ≠ rN by decide)]; exact hAV.hv⟩
  have hregs : ∀ q, q ≠ rT → q ≠ rE → q ≠ rV → ((τab.setv rN 0).setv rM 0).val q = 0 := by
    intro q a1 a2 a3
    rw [WState.setv_val, WState.setv_val]
    by_cases h1 : q = rM
    · subst h1; rw [Function.update_self]
    · rw [Function.update_of_ne h1]
      by_cases h2 : q = rN
      · subst h2; rw [Function.update_self]
      · rw [Function.update_of_ne h2]; exact hAV.regs q h2 h1 a2 a1 a3
  have hden : max (2 ^ eOf l F kclk coef A a ha r * vOf l F kclk coef A a ha r) 1 <
      2 ^ FinalPass.Sd.R.Tf l F kclk coef A a ha r := by
    rw [← denSplit l F kclk coef A a ha r]; exact FinalPass.Sd.R.fpDen_ltR l F kclk coef A a ha r
  obtain ⟨τd, nd, hnd, sd, hF⟩ := pd.run cap (FinalPass.Sd.R.Tf l F kclk coef A a ha r) (eOf l F kclk coef A a ha r)
    (vOf l F kclk coef A a ha r) B (frame (fpIn l F kclk coef A a ha r)) _ capd hden hDB hregs
  -- the bounds
  have hsum : FinalPass.Sd.R.Tf l F kclk coef A a ha r + eOf l F kclk coef A a ha r + vOf l F kclk coef A a ha r + 1
      ≤ (KTZ l F + KV l F + 2) * X ^ nwE l F.filterErrDeg := by
    have e1 : (KTZ l F + KV l F + 2) * X ^ nwE l F.filterErrDeg = KTZ l F * X ^ nwE l F.filterErrDeg +
        KV l F * X ^ nwE l F.filterErrDeg + 2 * X ^ nwE l F.filterErrDeg := by ring
    rw [e1]; omega
  have hpowD : (FinalPass.Sd.R.Tf l F kclk coef A a ha r + eOf l F kclk coef A a ha r + vOf l F kclk coef A a ha r + 1)
      ^ pd.D ≤ (KTZ l F + KV l F + 2) ^ pd.D * X ^ (nwE l F.filterErrDeg * pd.D) := by
    calc _ ≤ ((KTZ l F + KV l F + 2) * X ^ nwE l F.filterErrDeg) ^ pd.D := Nat.pow_le_pow_left hsum _
      _ = _ := by rw [mul_pow, ← pow_mul]
  have hdX : pd.C * (FinalPass.Sd.R.Tf l F kclk coef A a ha r + eOf l F kclk coef A a ha r +
      vOf l F kclk coef A a ha r + 1) ^ pd.D ≤ (pd.C * (KTZ l F + KV l F + 2) ^ pd.D) *
        X ^ nwDs x l pc pa pb pd F.filterErrDeg := by
    calc _ ≤ pd.C * ((KTZ l F + KV l F + 2) ^ pd.D * X ^ (nwE l F.filterErrDeg * pd.D)) := Nat.mul_le_mul_left _ hpowD
      _ ≤ pd.C * ((KTZ l F + KV l F + 2) ^ pd.D * X ^ nwDs x l pc pa pb pd F.filterErrDeg) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (liftS (by rw [hDs]; omega)))
      _ = _ := by ring
  have hXDs : X ≤ X ^ nwDs x l pc pa pb pd F.filterErrDeg := by
    calc X = X ^ 1 := (pow_one X).symm
      _ ≤ _ := liftS (by rw [hDs]; omega)
  have hCs : nwCs x l pc pa pb pd F = pc.Cs F + pa.Cs F + pb.Cs F + pd.C * (KTZ l F + KV l F + 2) ^ pd.D + 20 := rfl
  refine ⟨τd, _, ?_, Step.seq (Step.seq (Step.seq sc sab) sclr) sd, ?_, hF.hin, ?_, hF.heads, hF.regs⟩
  · rw [hCs]
    exact nw_bound nc nab _ nd _ (pc.Cs F) (pa.Cs F) (pb.Cs F) (pd.C * (KTZ l F + KV l F + 2) ^ pd.D)
      (Nat.one_le_pow _ _ (by omega))
      (le_trans hnc (Nat.mul_le_mul_left _ (liftS (by rw [hDs]; omega)))) hnab (by omega) (le_trans hnd hdX)
  · intro k
    match k with
    | ⟨0, _⟩ =>
      show τd.st (sW0 x) = frame (binary (FinalPass.Sd.R.Tf l F kclk coef A a ha r) 0)
      exact hF.hw0
    | ⟨1, _⟩ =>
      show τd.st (sW1 x) = frame (binary (FinalPass.Sd.R.Tf l F kclk coef A a ha r) (fpDen l F kclk coef A a ha r))
      rw [denSplit l F kclk coef A a ha r]
      exact hF.hw1
  · intro i hi hk
    refine le_trans (hF.resid i hi (hk ⟨0, by decide⟩) (hk ⟨1, by decide⟩)) ?_
    rw [hCs]
    have e1 : (pc.Cs F + pa.Cs F + pb.Cs F + pd.C * (KTZ l F + KV l F + 2) ^ pd.D + 20) *
        X ^ nwDs x l pc pa pb pd F.filterErrDeg = pc.Cs F * X ^ nwDs x l pc pa pb pd F.filterErrDeg +
        (pa.Cs F + pb.Cs F) * X ^ nwDs x l pc pa pb pd F.filterErrDeg +
        (pd.C * (KTZ l F + KV l F + 2) ^ pd.D) * X ^ nwDs x l pc pa pb pd F.filterErrDeg +
        20 * X ^ nwDs x l pc pa pb pd F.filterErrDeg := by ring
    rw [e1]
    omega

end Run

/-- **NW's assembly over (d) v4**: the four phases give the `NumsMJ l` (on any bank `x`). -/
noncomputable def numsOfPhases' (x : ℕ) (l : Literals) : NumsPh4.NumsOfPhases' x l := fun pc pa pb pd =>
  ⟨LNS x, LNR, _, fun F => nwM x l pc pa pb pd F, sIn x, sOutN x,
    fun k => by
      show (if k.val = 0 then sW0 x else sW1 x) ≠ sIn x
      split
      · exact fne (by rw [sW0_val, sIn_val]; decide)
      · exact fne (by rw [sW1_val, sIn_val]; decide),
    nwKc x l pc pa pb, nwDk x l pc pa pb, nwCs x l pc pa pb pd, nwDs x l pc pa pb pd,
    fun F kclk coef A a ha r σ hin hsh hbl hv hc => nwRun x l pc pa pb pd F kclk coef A a ha r σ hin hsh hbl hv hc⟩

/-- **The bank width, a function of `l`**: `max(DT + 3, d_b l)` with `d_b l = dX(TW l, NW l)` (the (b)). -/
def xNW (db : Literals → ℕ) (l : Literals) : ℕ := max (DataDock.DT + 3) (db l)

theorem xNW_a (db : Literals → ℕ) (l : Literals) : DataDock.DT + 3 ≤ xNW db l := le_max_left _ _
theorem xNW_b (db : Literals → ℕ) (l : Literals) : db l ≤ xNW db l := le_max_right _ _

/-- **NW** (`NumsMJ l`) from (c), (a) (built here) and the explicit (b) and (d) v4, on a bank `x ≥ DT + 3`. -/
noncomputable def nwOf (l : Literals) (x : ℕ) (hx : DataDock.DT + 3 ≤ x) (pb : NumsPh3.PhB x l)
    (pd : NumsPh4.PhD' x) : NumsMJ l :=
  numsOfPhases' x l (NumsC.phC3 x l) (phA3 x hx l) pb pd

end NearCubicWires.WireExponent3_5.UnionMachine.NumsA

end
