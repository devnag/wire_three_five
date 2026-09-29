import Proof.Wire_3_5.FinalPass.SdSet4

/-! # S4 (the seeds phase), part 32: the setup's two halves together (P3:3170-3178)

**`setRS = setR ; setS`**; **`setRS_spec`**: from a body state whose only nonzero registers are the prep's
(`sRp 0 … 15, 17, 18`, `IsPrepReg`), the state `setSOut (setROut σ H₀ H₁ T₀ T₁)`. `setROut`'s registers:
`setROut_val_other`, `setROut_sH`, `setROut_sTT`, `setROut_rP`, `setROut_cp`; its streams, heads and cell are `σ`'s.

Paper quantity of the main type: the seeds phase's loop-entry state (its static numbers and formatted streams). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false

namespace NearCubicWires.WireExponent3_5.FinalPass.Sd
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.FinalPass
open NearCubicWires.WireExponent3_5.PrimAsm

theorem ne_of_val {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b := fun e => h (congrArg Fin.val e)

section Body
variable {nw nn nsc nrs : ℕ}

/-- The setup's two halves. -/
def setRS : BP nw nn nsc nrs := .seq setR setS

theorem setROut_val_other (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (q : Fin (bnr nn nrs))
    (h1 : q ∉ (cps.map Prod.snd : List (Fin (bnr nn nrs)))) (h2 : q ≠ rP 0) (h3 : q ≠ rP 1) (h4 : q ≠ sH 0)
    (h5 : q ≠ sH 1) (h6 : q ≠ sTT 0) (h7 : q ≠ sTT 1) : (setROut σ H0 H1 T0 T1).val q = σ.val q := by
  simp only [setROut, WState.setv_val, Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
    Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2]
  exact cpApply_notin σ cps q h1

theorem setROut_lo (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (q : Fin (bnr nn nrs)) (hq : q.val < 44) :
    (setROut σ H0 H1 T0 T1).val q = σ.val q :=
  setROut_val_other σ H0 H1 T0 T1 q (notin_cps q (Or.inl (by omega))) (ne_of_val (show q.val ≠ 120 by omega))
    (ne_of_val (show q.val ≠ 121 by omega)) (ne_of_val (show q.val ≠ 44 by omega))
    (ne_of_val (show q.val ≠ 45 by omega)) (ne_of_val (show q.val ≠ 46 by omega))
    (ne_of_val (show q.val ≠ 47 by omega))

theorem setROut_sH (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 2) :
    (setROut σ H0 H1 T0 T1).val (sH k) = ![H0, H1] k := by
  fin_cases k <;> simp [setROut, Function.update_apply, sH, sTT, brg_iff]

theorem setROut_sTT (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 2) :
    (setROut σ H0 H1 T0 T1).val (sTT k) = ![T0 - 1, T1 - 1] k := by
  fin_cases k <;> simp [setROut, Function.update_apply, sTT, brg_iff]

theorem setROut_rP (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 2) :
    (setROut σ H0 H1 T0 T1).val (rP k) =
      ![if 1 ≤ σ.val (sRp 12) then 1 else 0, if 2 ≤ σ.val (sRp 12) then 1 else 0] k := by
  fin_cases k <;> simp [setROut, Function.update_apply, rP_b, sH, sTT, brg_iff]

theorem setROut_cp (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (p : Fin (bnr nn nrs) × Fin (bnr nn nrs))
    (hp : p ∈ (cps : List (Fin (bnr nn nrs) × Fin (bnr nn nrs)))) :
    (setROut σ H0 H1 T0 T1).val p.2 = σ.val p.1 := by
  have hne : p.2 ≠ rP 0 ∧ p.2 ≠ rP 1 ∧ p.2 ≠ sH 0 ∧ p.2 ≠ sH 1 ∧ p.2 ≠ sTT 0 ∧ p.2 ≠ sTT 1 := by
    simp only [cps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [ctrR_b, frD_b, rP_b, sH, sTT, brg_iff]
  obtain ⟨h2, h3, h4, h5, h6, h7⟩ := hne
  simp only [setROut, WState.setv_val, Function.update_of_ne h7, Function.update_of_ne h6, Function.update_of_ne h5,
    Function.update_of_ne h4, Function.update_of_ne h3, Function.update_of_ne h2]
  exact cpApply_in σ cps cps_nodup cps_sd p hp

theorem setROut_st (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) : (setROut σ H0 H1 T0 T1).st = σ.st := by
  simp only [setROut, WState.setv_st]; exact cpApply_st σ cps

theorem setROut_sh (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) : (setROut σ H0 H1 T0 T1).sh = σ.sh := by
  simp only [setROut, WState.setv_sh]; exact cpApply_sh σ cps

theorem setROut_cell (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) : (setROut σ H0 H1 T0 T1).cell = σ.cell := by
  simp only [setROut, WState.setv_cell]; exact cpApply_cell σ cps

/-- The prep's registers that hold values: `sRp 0 … 15, 17, 18`. -/
def IsPrepReg (q : Fin (bnr nn nrs)) : Prop := ∃ k : Fin 30, k.val ≠ 16 ∧ k.val < 19 ∧ q = sRp k

theorem setZ_notPrep (q : Fin (bnr nn nrs)) (hq : q ∈ (setZ : List (Fin (bnr nn nrs)))) : ¬ IsPrepReg q := by
  rintro ⟨k, _, h19, rfl⟩
  simp only [setZ, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
    (have := congrArg Fin.val h; simp [sRp_b, ctrR_b, frD_b, rP_b, sK, sT, sOP, sC, sH, sTT, sX, brg] at this <;>
      omega)

theorem setRS_spec (cap : ℕ) (σ : BS nw nn nsc nrs) (H0 H1 : ℕ) (w0 w1 rest : List Bool)
    (hR : ∀ q, ¬ IsPrepReg q → σ.val q = 0) (hv : ∀ k : Fin 30, 8 * σ.val (sRp k) + 1 ≤ cap)
    (hG0 : (∃ w rest, σ.st (tG 0) = true :: (frameP w ++ false :: rest) ∧ w.length = H0) ∨
      (readTapeBit (σ.st (tG 0)) 0 = false ∧ H0 = 0))
    (hG1 : (∃ w rest, σ.st (tG 1) = true :: (frameP w ++ false :: rest) ∧ w.length = H1) ∨
      (readTapeBit (σ.st (tG 1)) 0 = false ∧ H1 = 0))
    (hsG : ∀ k : Fin 2, σ.sh (tG k) = 0)
    (hTW : σ.st tTW = frameP w0 ++ false :: (frameP w1 ++ false :: rest)) (hsTW : σ.sh tTW = 0)
    (hE : ∀ j ∈ (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))), σ.st j.o = [] ∧ σ.sh j.o = 0)
    (hSp : σ.st tSp = []) (hSph : σ.sh tSp = 0)
    (hc : 8 * H0 + 8 * H1 + 8 * w0.length + 8 * w1.length + 10 ≤ cap) :
    ∃ m, WExec cap setRS σ (setSOut (setROut σ H0 H1 w0.length w1.length)) m ∧
      m ≤ setRCost σ H0 H1 w0.length w1.length +
        (flJobsCost (setROut σ H0 H1 w0.length w1.length) sJobs + 1 +
          (1 + 1 + (sClr.map fun r => 3 * (setROut σ H0 H1 w0.length w1.length).val r + 2).sum)) + 1 := by
  have hz : ∀ q ∈ (setZ : List (Fin (bnr nn nrs))), σ.val q = 0 := fun q hq => hR q (setZ_notPrep q hq)
  obtain ⟨m1, e1, hm1⟩ := setR_spec cap σ H0 H1 w0 w1 rest hz (fun k => by have := hv k; omega) hG0 hG1 hsG hTW
    hsTW (by omega)
  obtain ⟨σR, gR⟩ : ∃ y : BS nw nn nsc nrs, y = setROut σ H0 H1 w0.length w1.length := ⟨_, rfl⟩
  rw [← gR] at e1 ⊢
  have sR : σR.st = σ.st := by rw [gR]; exact setROut_st σ _ _ _ _
  have hR' : σR.sh = σ.sh := by rw [gR]; exact setROut_sh σ _ _ _ _
  have vlo : ∀ q : Fin (bnr nn nrs), q.val < 44 → σR.val q = σ.val q := fun q hq => by
    rw [gR]; exact setROut_lo σ _ _ _ _ q hq
  have vRp : ∀ k : Fin 30, σR.val (sRp k) = σ.val (sRp k) := fun k => vlo _ (show 10 + k.val < 44 by omega)
  have hv' : ∀ k : Fin 30, σ.val (sRp k) ≤ cap := fun k => by have := hv k; omega
  have vH0 : σR.val (sH 0) = H0 := by rw [gR, setROut_sH]; rfl
  have vH1 : σR.val (sH 1) = H1 := by rw [gR, setROut_sH]; rfl
  have vT0 : σR.val (sTT 0) = w0.length - 1 := by rw [gR, setROut_sTT]; rfl
  have vT1 : σR.val (sTT 1) = w1.length - 1 := by rw [gR, setROut_sTT]; rfl
  have vK : σR.val sK = 0 := by rw [vlo sK (show 40 < 44 by omega)]; exact hz _ (by simp [setZ])
  have vt : σR.val sT = 0 := by rw [vlo sT (show 41 < 44 by omega)]; exact hz _ (by simp [setZ])
  have vO : σR.val sOP = 0 := by rw [vlo sOP (show 42 < 44 by omega)]; exact hz _ (by simp [setZ])
  have e2 := setS_spec cap σR (fun j hj => by rw [sR, hR']; exact hE j hj) (by rw [sR]; exact hSp)
    (by rw [hR']; exact hSph) vK vt vO
    (fun j hj => by
      simp only [sJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        dsimp only <;>
        first
          | (rw [vRp]; exact hv _)
          | (rw [vH0]; omega)
          | (rw [vH1]; omega)
          | (rw [vT0]; omega)
          | (rw [vT1]; omega))
    (fun q hq => by
      simp only [sClr, List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | (rw [vRp]; exact hv' _)
          | (rw [vH0]; omega)
          | (rw [vH1]; omega)
          | (rw [vT0]; omega)
          | (rw [vT1]; omega))
  exact ⟨_, WExec.seq e1 e2, by omega⟩

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
