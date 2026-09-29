import Proof.Wire_3_5.FinalPass.SdSet5

/-! # S4 (the seeds phase), part 33: the setup's exit, read off (P3:3170-3178)

The state `setSOut (setROut σ H₀ H₁ T₀ T₁)` of `setRS_spec`, from a body state whose only nonzero registers are the
prep's: every register off `seedFix` (the star parameters `ctrR 0 … 4`, the digits `frD 0 … 3`, the flags `rP k`)
is `0` (**`setRS_val_zero`**), those hold their numbers (`setRS_ctrR`, `setRS_frD`, `setRS_rP`); the formatted
streams (`setRS_tU` … `setRS_tT`, `setRS_tSp`) and every other stream as before (**`setRS_st_other`**), the heads
and the cell as before.

Paper quantity of the main type: the seeds phase's loop-entry state (static numbers, formatted streams). -/

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

section Body
variable {nw nn nsc nrs : ℕ}

/-- The registers the setup leaves nonzero. -/
def seedFix : List (Fin (bnr nn nrs)) := [ctrR 0, ctrR 1, ctrR 2, ctrR 3, ctrR 4, frD 0, frD 1, frD 2, frD 3, rP 0, rP 1]

theorem prepReg_sClr (q : Fin (bnr nn nrs)) (h : IsPrepReg q) : q ∈ (sClr : List (Fin (bnr nn nrs))) := by
  obtain ⟨k, h16, h19, rfl⟩ := h
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨
      k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 ∨ k = 17 ∨ k = 18 := by
    have := k.isLt
    rcases k with ⟨v, hv⟩
    simp only [Fin.ext_iff] at *
    omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl <;> simp [sClr]

theorem setSOut_val (σ : BS nw nn nsc nrs) (q : Fin (bnr nn nrs)) :
    (setSOut σ).val q = if q ∈ (sClr : List (Fin (bnr nn nrs))) then 0 else σ.val q := by
  rw [setSOut, clApply_val]
  simp [flApply_val]

theorem setSOut_st (σ : BS nw nn nsc nrs) :
    (setSOut σ).st = Function.update (flApply σ sJobs).st tSp [true] := by
  rw [setSOut, clApply_st]
  simp

theorem setSOut_sh (σ : BS nw nn nsc nrs) : (setSOut σ).sh = σ.sh := by
  rw [setSOut, clApply_sh]; simp [flApply_sh]

theorem setSOut_cell (σ : BS nw nn nsc nrs) : (setSOut σ).cell = σ.cell := by
  rw [setSOut, clApply_cell]; simp [flApply_cell]

theorem setRS_val_zero (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (hR : ∀ q, ¬ IsPrepReg q → σ.val q = 0)
    (q : Fin (bnr nn nrs)) (hq : q ∉ (seedFix : List (Fin (bnr nn nrs)))) :
    (setSOut (setROut σ H0 H1 T0 T1)).val q = 0 := by
  rw [setSOut_val]
  by_cases hc : q ∈ (sClr : List (Fin (bnr nn nrs)))
  · rw [if_pos hc]
  · rw [if_neg hc]
    have h1 : q ∉ (cps.map Prod.snd : List (Fin (bnr nn nrs))) := by
      intro h
      apply hq
      simp only [cps, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at h
      simp only [seedFix, List.mem_cons, List.not_mem_nil, or_false]
      tauto
    have hS : ∀ x ∈ (sClr : List (Fin (bnr nn nrs))), q ≠ x := fun x hx e => hc (e ▸ hx)
    rw [setROut_val_other σ H0 H1 T0 T1 q h1 (fun e => hq (by rw [e]; simp [seedFix]))
      (fun e => hq (by rw [e]; simp [seedFix])) (hS _ (by simp [sClr])) (hS _ (by simp [sClr]))
      (hS _ (by simp [sClr])) (hS _ (by simp [sClr]))]
    exact hR q (fun hp => hc (prepReg_sClr q hp))

theorem setRS_cp (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (p : Fin (bnr nn nrs) × Fin (bnr nn nrs))
    (hp : p ∈ (cps : List (Fin (bnr nn nrs) × Fin (bnr nn nrs)))) :
    (setSOut (setROut σ H0 H1 T0 T1)).val p.2 = σ.val p.1 := by
  have hc : p.2 ∉ (sClr : List (Fin (bnr nn nrs))) := by
    simp only [cps, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [sClr, ctrR_b, frD_b, sRp_b, sH, sTT, brg_iff]
  rw [setSOut_val, if_neg hc, setROut_cp σ H0 H1 T0 T1 p hp]

theorem setRS_rP (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 2) :
    (setSOut (setROut σ H0 H1 T0 T1)).val (rP k) =
      ![if 1 ≤ σ.val (sRp 12) then 1 else 0, if 2 ≤ σ.val (sRp 12) then 1 else 0] k := by
  have hc : rP k ∉ (sClr : List (Fin (bnr nn nrs))) := by
    fin_cases k <;> simp [sClr, rP_b, sRp_b, sH, sTT, brg_iff]
  rw [setSOut_val, if_neg hc, setROut_rP]

/-- The formatted streams: a job's word at the register half's exit. -/
theorem setRS_st_job (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (j : FlJob (bns nw nsc) (bnr nn nrs))
    (hj : j ∈ (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs)))) :
    (setSOut (setROut σ H0 H1 T0 T1)).st j.o = flOut (setROut σ H0 H1 T0 T1) j := by
  have hm : j.o ∈ ((sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))).map FlJob.o) := List.mem_map_of_mem hj
  have hne : j.o ≠ tSp := fun e => tSp_notin (e ▸ hm)
  rw [setSOut_st, Function.update_of_ne hne, flApply_st_in _ _ sJobs_nodup j hj]

theorem setRS_st_Sp (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) :
    (setSOut (setROut σ H0 H1 T0 T1)).st tSp = [true] := by
  rw [setSOut_st, Function.update_self]

theorem setRS_st_other (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (i : Fin (bns nw nsc + 1))
    (hi : i ∉ ((sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))).map FlJob.o)) (hS : i ≠ tSp) :
    (setSOut (setROut σ H0 H1 T0 T1)).st i = σ.st i := by
  rw [setSOut_st, Function.update_of_ne hS, flApply_st_notin _ _ i hi, setROut_st]

theorem setRS_sh (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) : (setSOut (setROut σ H0 H1 T0 T1)).sh = σ.sh := by
  rw [setSOut_sh, setROut_sh]

theorem setRS_cell (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) :
    (setSOut (setROut σ H0 H1 T0 T1)).cell = σ.cell := by
  rw [setSOut_cell, setROut_cell]

/-! ## The formatted streams, in their loops' forms -/

theorem flOut_rp (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (o : Fin (bns nw nsc + 1)) (k : Fin 30)
    (bs : List Bool) (e : Bool) :
    flOut (setROut σ H0 H1 T0 T1) ⟨o, sRp k, bs, e⟩ = (List.replicate (σ.val (sRp k)) bs).flatten ++ [e] := by
  unfold flOut
  rw [setROut_lo σ H0 H1 T0 T1 (sRp k) (show 10 + k.val < 44 by omega)]

theorem setRS_frame (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (o : Fin (bns nw nsc + 1)) (k : Fin 30)
    (hj : (⟨o, sRp k, [true, false], false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈ sJobs) :
    (setSOut (setROut σ H0 H1 T0 T1)).st o = frame (List.replicate (σ.val (sRp k)) false) := by
  rw [setRS_st_job σ H0 H1 T0 T1 _ hj, flOut_rp σ H0 H1 T0 T1 o k, flZf]

theorem setRS_tPos (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 2) :
    (setSOut (setROut σ H0 H1 T0 T1)).st (tPos k) = frame (List.replicate (![H0, H1] k) false) ∧
      (setSOut (setROut σ H0 H1 T0 T1)).st (tNeg k) = frame (List.replicate (![H0, H1] k) false) := by
  have hP : (⟨tPos k, sH k, [true, false], false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈ sJobs := by
    fin_cases k <;> simp [sJobs]
  have hN : (⟨tNeg k, sH k, [true, false], false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈ sJobs := by
    fin_cases k <;> simp [sJobs]
  rw [setRS_st_job σ H0 H1 T0 T1 _ hP, setRS_st_job σ H0 H1 T0 T1 _ hN]
  unfold flOut
  simp only [setROut_sH]
  exact ⟨flZf _, flZf _⟩

theorem setRS_tX (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 2) :
    (setSOut (setROut σ H0 H1 T0 T1)).st (tX k) =
      (List.replicate (σ.val (sRp ⟨9 + k.val, by omega⟩)) (List.replicate 8 false)).flatten ++ [false] ∧
    (setSOut (setROut σ H0 H1 T0 T1)).st (tZ k) =
      (List.replicate (σ.val (sRp ⟨9 + k.val, by omega⟩)) [false, false]).flatten ++ [false] := by
  have hX : (⟨tX k, sRp ⟨9 + k.val, by omega⟩, List.replicate 8 false, false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈
      sJobs := by
    fin_cases k <;> simp [sJobs]
  have hZ : (⟨tZ k, sRp ⟨9 + k.val, by omega⟩, [false, false], false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈
      sJobs := by
    fin_cases k <;> simp [sJobs]
  rw [setRS_st_job σ H0 H1 T0 T1 _ hX, setRS_st_job σ H0 H1 T0 T1 _ hZ, flOut_rp σ H0 H1 T0 T1,
    flOut_rp σ H0 H1 T0 T1]
  exact ⟨rfl, rfl⟩

theorem setRS_tT (σ : BS nw nn nsc nrs) (H0 H1 T0 T1 : ℕ) (k : Fin 2) :
    (setSOut (setROut σ H0 H1 T0 T1)).st (tT k) =
      (List.replicate (![T0 - 1, T1 - 1] k) [false]).flatten ++ [false] := by
  have hT : (⟨tT k, sTT k, [false], false⟩ : FlJob (bns nw nsc) (bnr nn nrs)) ∈ sJobs := by
    fin_cases k <;> simp [sJobs]
  rw [setRS_st_job σ H0 H1 T0 T1 _ hT]
  unfold flOut
  simp only [setROut_sTT]

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
