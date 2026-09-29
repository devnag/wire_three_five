import Proof.Wire_3_5.Primitive.SeedFix.C4KWe

/-! # C4KW, part 6: the stage B4 (the framed HASH tape and populations)

`b4P` (streams: `0`, `1` the outputs, `2`, `3` the inputs `htWord Fs`, `popsWord pops`): the HASH tape's framed copy,
its terminator, the populations' framed copy, its terminator. **`b4_run`**: from the stage's entry, the kept words `3`,
`4` framed on the outputs, the inputs kept. **`partB4 : PartB4`**.

Paper quantity of the main type: the Hb printer's static streams `htWord Fs`, `popsWord pops` (P3:2253-2290), framed. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.PrimT.C4KW
open NearCubicWires NearCubicWires.WireExponent3_5 NearCubicWires.RepairOrdinary NearCubicWires.LocalBitMultitape
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.PrimT.C4H
open NearCubicWires.WireExponent3_5.PrimT.C4Hk (apd apd_nil apd_apd apd_seth apd_sh_d apd_st_d apd_st_ne apd_sh_ne
  wlist wlist_spec)

noncomputable section

/-- **B4's word program**. -/
def b4P : WM 3 0 := .seq (htCopy 2 0) (.seq (wlist 0 [false]) (.seq (popsCopy 3 1) (wlist 1 [false])))

/-- B4's program steps. -/
def b4n (D : HashData) : ℕ :=
  (203 * (HbM.htWord D.Fs).length + 13) + 1 + (4 + 1 + ((70 * (HbM.popsWord D.pops).length + 13) + 1 + 4))

theorem b4_run (D : HashData) (cap : ℕ) :
    ∃ τ : WState 3 0, WExec 0 b4P (st0' (no := 2) iB4 D cap) τ (b4n D) ∧ τ.cell = false ∧
      τ.st 0 = frame (HbM.htWord D.Fs) ∧ τ.st 1 = frame (HbM.popsWord D.pops) ∧
      τ.st 2 = HbM.htWord D.Fs ∧ τ.st 3 = HbM.popsWord D.pops := by
  set σ0 : WState 3 0 := st0' (no := 2) iB4 D cap with hσ0
  have s2 : σ0.st 2 = HbM.htWord D.Fs := rfl
  have s3 : σ0.st 3 = HbM.popsWord D.pops := rfl
  have s0 : σ0.st 0 = [] := rfl
  have s1 : σ0.st 1 = [] := rfl
  have t1 := cp_ht (cap := 0) (S := 2) (O := 0) (by decide) D.Fs σ0 [] [] (by rw [s2]; simp) rfl rfl
  set σ1 := (apd σ0 0 (prs (HbM.htWord D.Fs))).seth 2 ([].length + (HbM.htWord D.Fs).length) with hσ1
  have t2 := wlist_spec 0 0 [false] σ1 (by
    rw [hσ1]; simp only [WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (by decide), apd_sh_d, apd_st_d, List.length_append])
  set σ2 := apd σ1 0 [false] with hσ2
  have t3 := cp_pops (cap := 0) (S := 3) (O := 1) (by decide) D.pops σ2 [] []
    (by rw [hσ2, apd_st_ne _ _ _ (by decide), hσ1]; simp only [WState.seth_st]; rw [apd_st_ne _ _ _ (by decide), s3]; simp)
    (by rw [hσ2, apd_sh_ne _ _ _ (by decide), hσ1]; simp only [WState.seth_sh]
        rw [Function.update_of_ne (by decide), apd_sh_ne _ _ _ (by decide)]; rfl)
    (by rw [hσ2, apd_sh_ne _ _ _ (by decide), apd_st_ne _ _ _ (by decide), hσ1]; simp only [WState.seth_sh,
          WState.seth_st]
        rw [Function.update_of_ne (by decide), apd_sh_ne _ _ _ (by decide), apd_st_ne _ _ _ (by decide)]; rfl)
  set σ3 := (apd σ2 1 (prs (HbM.popsWord D.pops))).seth 3 ([].length + (HbM.popsWord D.pops).length) with hσ3
  have t4 := wlist_spec 0 1 [false] σ3 (by
    rw [hσ3]; simp only [WState.seth_sh, WState.seth_st]
    rw [Function.update_of_ne (by decide), apd_sh_d, apd_st_d, List.length_append])
  refine ⟨apd σ3 1 [false], WExec.cast 0 (WExec.seq t1 (WExec.seq t2 (WExec.seq t3 t4))) rfl
    (by unfold b4n; simp only [List.length_singleton]; omega), rfl, ?_, ?_, ?_, ?_⟩
  · rw [apd_st_ne _ _ _ (by decide), hσ3]; simp only [WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ2, apd_st_d, hσ1]; simp only [WState.seth_st]
    rw [apd_st_d, s0, frame_prs]; rfl
  · rw [apd_st_d, hσ3]; simp only [WState.seth_st]
    rw [apd_st_d, hσ2, apd_st_ne _ _ _ (by decide), hσ1]; simp only [WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), s1, frame_prs]; rfl
  · rw [apd_st_ne _ _ _ (by decide), hσ3]; simp only [WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ2, apd_st_ne _ _ _ (by decide), hσ1]; simp only [WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), s2]
  · rw [apd_st_ne _ _ _ (by decide), hσ3]; simp only [WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), hσ2, apd_st_ne _ _ _ (by decide), hσ1]; simp only [WState.seth_st]
    rw [apd_st_ne _ _ _ (by decide), s3]

theorem b4_le (D : HashData) (cap : ℕ) : 2 * b4n D + 2 ≤ 600 * (kwS D cap + 1) ^ 2 + 600 * (kwT D + 1) ^ 0 := by
  have h1 : (HbM.htWord D.Fs).length + (HbM.popsWord D.pops).length ≤ kwS D cap := by unfold kwS; omega
  have h2 : kwS D cap + 1 ≤ (kwS D cap + 1) ^ 2 := by nlinarith
  unfold b4n
  omega

/-- **B4** (the framed copies of the HASH tape and the populations). -/
def partB4 : PartB4 where
  x := 2
  s := _
  M := partM (no := 2) (ni := 2) (ns := 3) (nr := 0) (x := 2) (by norm_num) (by norm_num) b4P
  cost := fun D _ => 2 * b4n D + 2
  K := 600
  Dg := 0
  cost_le := b4_le
  run := fun D cap => by
    obtain ⟨τ, hw, hc, h0, h1, h2, h3⟩ := b4_run D cap
    refine part_run (no := 2) (ni := 2) (ns := 3) (nr := 0) (x := 2) (by norm_num) (by norm_num) (by norm_num) oB4 iB4
      b4P D cap 0 τ (b4n D) hw hc (fun r => Fin.elim0 r) (Nat.zero_le _) (fun j => ?_) (fun k => ?_)
      (fun i hi => absurd i.isLt (by omega))
    · fin_cases j
      · exact h0
      · exact h1
    · fin_cases k
      · exact h2
      · exact h3

end

end NearCubicWires.WireExponent3_5.PrimT.C4KW
