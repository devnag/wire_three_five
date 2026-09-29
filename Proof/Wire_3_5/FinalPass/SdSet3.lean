import Proof.Wire_3_5.FinalPass.SdSet2

/-! # S4 (the seeds phase), part 30: the setup's stream half, on the body (P3:3170-3178)

**`setS`**: the fills `sJobs` (the point's three streams `tU, tV, tC` to `n` framed zeros, the counters `tRow`,
`tCol` to `dRow`, `dR` framed zeros, per carrier `tX k` to `8·Lₖ` zeros, `tZ k` to `2·Lₖ` zeros, `tPos k`, `tNeg k`
to `Hₖ` framed zeros, the tables `tT k` to `Tₖ` zeros, each then its end bit), `tSp := [true]`, then the prep's and
the register half's registers cleared (`sClr`). **`setS_spec`**: the state
`clApply ((flApply σ sJobs).sets tSp [true]) sClr`.

Paper quantity of the main type: the seeds phase's formatted working streams at its loops' entry. -/

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

theorem bst_iff {a b : ℕ} (ha : a < 47) (hb : b < 47) :
    (bst a ha : Fin (bns nw nsc + 1)) = bst b hb ↔ a = b := by
  simp [bst, Fin.ext_iff]

/-- The fills. -/
def sJobs : List (FlJob (bns nw nsc) (bnr nn nrs)) :=
  [⟨tU, sRp 17, [true, false], false⟩, ⟨tV, sRp 17, [true, false], false⟩, ⟨tC, sRp 17, [true, false], false⟩,
    ⟨tRow, sRp 7, [true, false], false⟩, ⟨tCol, sRp 8, [true, false], false⟩,
    ⟨tX 0, sRp 9, List.replicate 8 false, false⟩, ⟨tX 1, sRp 10, List.replicate 8 false, false⟩,
    ⟨tZ 0, sRp 9, [false, false], false⟩, ⟨tZ 1, sRp 10, [false, false], false⟩,
    ⟨tPos 0, sH 0, [true, false], false⟩, ⟨tNeg 0, sH 0, [true, false], false⟩,
    ⟨tPos 1, sH 1, [true, false], false⟩, ⟨tNeg 1, sH 1, [true, false], false⟩,
    ⟨tT 0, sTT 0, [false], false⟩, ⟨tT 1, sTT 1, [false], false⟩]

/-- The registers cleared at the end. -/
def sClr : List (Fin (bnr nn nrs)) :=
  [sRp 0, sRp 1, sRp 2, sRp 3, sRp 4, sRp 5, sRp 6, sRp 7, sRp 8, sRp 9, sRp 10, sRp 11, sRp 12, sRp 13, sRp 14,
    sRp 15, sRp 17, sRp 18, sH 0, sH 1, sTT 0, sTT 1]

theorem sJobs_nodup : ((sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))).map FlJob.o).Nodup := by
  simp [sJobs, tU, tV, tC, tRow, tCol, tX, tZ, tPos, tNeg, tT, bst_iff]

theorem sJobs_facts : ∀ j ∈ (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))),
    j.v ≠ sK ∧ j.v ≠ sT ∧ j.bs.length ≤ 8 := by
  intro j hj
  simp only [sJobs, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [sRp_b, sK, sT, sH, sTT, brg_iff]

theorem tSp_notin : (tSp : Fin (bns nw nsc + 1)) ∉
    ((sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))).map FlJob.o) := by
  simp [sJobs, tSp, tU, tV, tC, tRow, tCol, tX, tZ, tPos, tNeg, tT, bst_iff]

theorem sClr_nodup : (sClr : List (Fin (bnr nn nrs))).Nodup := by
  simp [sClr, sRp_b, sH, sTT, brg_iff]

/-- The stream half. -/
def setS : BP nw nn nsc nrs := .seq (flJobs sOP sK sT sJobs) (.seq (.wr tSp true) (clJobs sClr))

/-- The stream half's exit. -/
def setSOut (σ : BS nw nn nsc nrs) : BS nw nn nsc nrs := clApply ((flApply σ sJobs).sets tSp [true]) sClr

theorem setS_spec (cap : ℕ) (σ : BS nw nn nsc nrs)
    (hE : ∀ j ∈ (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))), σ.st j.o = [] ∧ σ.sh j.o = 0)
    (hSp : σ.st tSp = []) (hSph : σ.sh tSp = 0) (hK : σ.val sK = 0) (ht : σ.val sT = 0) (hO : σ.val sOP = 0)
    (hc : ∀ j ∈ (sJobs : List (FlJob (bns nw nsc) (bnr nn nrs))), 8 * σ.val j.v + 1 ≤ cap)
    (hcl : ∀ q ∈ (sClr : List (Fin (bnr nn nrs))), σ.val q ≤ cap) :
    WExec cap setS σ (setSOut σ)
      (flJobsCost σ sJobs + 1 + (1 + 1 + (sClr.map fun r => 3 * σ.val r + 2).sum)) := by
  have e1 := flJobs_spec cap sOP sK sT (by simp [sK, sOP, brg_iff]) (by simp [sK, sT, brg_iff]) sJobs σ sJobs_nodup
    (fun j hj => by
      obtain ⟨f1, f2, f3⟩ := sJobs_facts j hj
      have hm : σ.val j.v * j.bs.length ≤ σ.val j.v * 8 := Nat.mul_le_mul_left _ f3
      have := hc j hj
      exact ⟨(hE j hj).1, (hE j hj).2, f1, f2, by omega, by omega⟩)
    hK ht hO
  have hw : writeTapeBit ((flApply σ sJobs).st tSp) ((flApply σ sJobs).sh tSp) true = [true] := by
    rw [flApply_st_notin σ sJobs tSp tSp_notin, flApply_sh, hSp, hSph]
    rfl
  have e2 := WExec.wr (cap := cap) tSp true (flApply σ sJobs)
  rw [hw] at e2
  have hv9 : ((flApply σ sJobs).sets tSp [true]).val = σ.val := by rw [WState.sets_val, flApply_val]
  have e3 := clJobs_spec cap sClr ((flApply σ sJobs).sets tSp [true]) sClr_nodup
    (fun q hq => by rw [hv9]; exact hcl q hq)
  rw [hv9] at e3
  exact WExec.seq e1 (WExec.seq e2 e3)

end Body

end NearCubicWires.WireExponent3_5.FinalPass.Sd
