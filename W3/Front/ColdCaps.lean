import W3.Front.ColdPhases

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)

namespace W3.NearCubicWires.RepairSource.Outer3.Front

section CapMaps
variable (pB pU : Program) (Dc : ℕ) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  {mw : Outer.MWSource} {SV : Outer.SuccinctVerifier H0 G0} (F : FrontSpecD mw SV)

theorem mOC_val (k : Fin 2) (j : Fin 40) : (mOC pB pU (tCap Dc) F k j).val =
    if j.val = 0 then 17 + 11 * k.val else if j.val = 32 then 19 + 11 * k.val else if j.val = 36 then 20 + 11 * k.val
    else bOC pB.tapeCount pU.tapeCount k + j.val := by
  unfold mOC; split_ifs <;> simp [fs, cs, blk] <;> omega

theorem mOC_inj (k : Fin 2) : Function.Injective (mOC pB pU (tCap Dc) F k) := by
  intro i j h; have hv := congrArg Fin.val h; rw [mOC_val, mOC_val] at hv
  have := i.isLt; have := j.isLt; have := k.isLt; unfold bOC at hv
  apply Fin.ext; split_ifs at hv <;> omega

theorem mCAP_val (k : Fin 2) (j : Fin (tCap Dc)) : (mCAP pB pU Dc F k j).val =
    if j.val = 0 then 20 + 11 * k.val else if j.val = 1 then 19 + 11 * k.val
    else if j.val = CloseoutWitness.OracleCap.Core.P Dc + 4 then 21 + 11 * k.val
    else bCAP pB.tapeCount pU.tapeCount (tCap Dc) k + j.val := by
  unfold mCAP; split_ifs <;> simp [fs, cs, blk] <;> omega

theorem mCAP_inj (k : Fin 2) : Function.Injective (mCAP pB pU Dc F k) := by
  intro i j h; have hv := congrArg Fin.val h; rw [mCAP_val, mCAP_val] at hv
  have := i.isLt; have := j.isLt; have := k.isLt; unfold bCAP at hv
  apply Fin.ext; split_ifs at hv <;> omega

theorem mF_val (j : Fin F.t) : (mF pB pU Dc F j).val =
    if j = F.zIn then 10 else if j = F.sIn then 17 else if j = F.pIn then 28
    else bF pB.tapeCount pU.tapeCount (tCap Dc) + j.val := by
  unfold mF; split_ifs <;> rfl

theorem mF_inj : Function.Injective (mF pB pU Dc F) := by
  have nd := F.inputs_nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  intro i j h; have hv := congrArg Fin.val h; rw [mF_val, mF_val] at hv
  have := i.isLt; have := j.isLt; unfold bF at hv
  split_ifs at hv <;> first | (subst_vars; rfl) | (exfalso; omega) | (exact Fin.ext (by omega))

end CapMaps

section Cap
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

/-- One circuit's cap: `CF_k := [decide (|c| ≤ q^G)]`, keeping `DD_k`. -/
theorem capOne_exec (k : Fin 2) {q : ℕ} (c : BooleanCircuit q) (cap : ℕ) (σ : WState (NSC mw SV F degree) nrW)
    (hDD : σ.st (fsC mw SV F degree k 6 (by decide)) = PCPPNative.descriptor c)
    (hDDh : σ.sh (fsC mw SV F degree k 6 (by decide)) = 0)
    (hfresh : ∀ (i : ℕ) (h : i < 11), 8 ≤ i → σ.st (fsC mw SV F degree k i h) = [] ∧
      σ.sh (fsC mw SV F degree k i h) = 0)
    (hOC : ∀ i : Fin (NSC mw SV F degree + 1), bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k ≤ i.val →
      i.val < bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k + 40 → σ.st i = [] ∧ σ.sh i = 0)
    (hCAP : ∀ i : Fin (NSC mw SV F degree + 1),
      bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k ≤ i.val →
      i.val < bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k + tCap (Dc degree) →
      σ.st i = [] ∧ σ.sh i = 0) :
    ∃ τ, WXExec cap (.seq (.mach PCPPNativeOracleCold.machine (mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k))
        (.mach (CloseoutWitness.OracleCap.machine degree) (mCAP (progB mw SV) (progU mw SV) (Dc degree) F k))) σ τ
        (PCPPNativeOracleCold.budget q c.size + 1 + CloseoutWitness.OracleCap.budget degree q c.size) ∧
      τ.st (fsC mw SV F degree k 10 (by decide)) =
        [decide (c.size ≤ RecoveryScheduleEnvelope.oracleSizeBound degree q)] ∧
      τ.sh (fsC mw SV F degree k 10 (by decide)) = 0 ∧
      τ.st (fsC mw SV F degree k 6 (by decide)) = PCPPNative.descriptor c ∧
      τ.sh (fsC mw SV F degree k 6 (by decide)) = 0 ∧
      (∀ i : Fin (NSC mw SV F degree + 1), (i.val < 17 + 11 * k.val ∨ 22 + 11 * k.val ≤ i.val) →
        (i.val < bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k ∨
          bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k + 40 ≤ i.val) →
        (i.val < bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k ∨
          bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k + tCap (Dc degree) ≤ i.val) →
        τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      τ.val = σ.val ∧ τ.cell = σ.cell := by
  classical
  have hk := k.isLt
  obtain ⟨o1, hr1, ho0, ho32, ho36, -, -⟩ := PCPPNativeOracleCold.oracle_run c
  have hOCv := mOC_val (progB mw SV) (progU mw SV) (Dc degree) F k
  have hbO : 33 ≤ bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k := by unfold bOC; omega
  have e1 := mach_ready cap hr1 (mOC_inj (progB mw SV) (progU mw SV) (Dc degree) F k) σ (by
      intro j
      have hv := hOCv j
      have hj := j.isLt
      by_cases j0 : j.val = 0
      · have he : mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = fsC mw SV F degree k 6 (by decide) :=
          Fin.ext (by rw [hv, if_pos j0]; simp; omega)
        rw [he]; exact hDDh
      by_cases j32 : j.val = 32
      · have he : mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = fsC mw SV F degree k 8 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_pos j32]; simp; omega)
        rw [he]; exact (hfresh 8 (by decide) (by decide)).2
      by_cases j36 : j.val = 36
      · have he : mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = fsC mw SV F degree k 9 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_neg j32, if_pos j36]; simp; omega)
        rw [he]; exact (hfresh 9 (by decide) (by decide)).2
      exact (hOC _ (by rw [hv]; simp [j0, j32, j36]) (by rw [hv]; simp [j0, j32, j36])).2)
    (by
      intro j
      have hv := hOCv j
      have hj := j.isLt
      unfold PCPPNativeOracleCold.input
      by_cases j0 : j.val = 0
      · have he : mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = fsC mw SV F degree k 6 (by decide) :=
          Fin.ext (by rw [hv, if_pos j0]; simp; omega)
        rw [he, if_pos (Fin.ext j0)]; exact hDD
      rw [if_neg (fun e => j0 (by rw [e]; rfl))]
      by_cases j32 : j.val = 32
      · have he : mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = fsC mw SV F degree k 8 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_pos j32]; simp; omega)
        rw [he]; exact (hfresh 8 (by decide) (by decide)).1
      by_cases j36 : j.val = 36
      · have he : mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = fsC mw SV F degree k 9 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_neg j32, if_pos j36]; simp; omega)
        rw [he]; exact (hfresh 9 (by decide) (by decide)).1
      exact (hOC _ (by rw [hv]; simp [j0, j32, j36]) (by rw [hv]; simp [j0, j32, j36])).1)
  set σ1 := updS (mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k) σ (fun _ => 0) o1 with hσ1
  have injO := mOC_inj (progB mw SV) (progU mw SV) (Dc degree) F k
  have mO : ∀ (j : Fin 40) (i : ℕ) (h : i < 11), j.val = (if i = 6 then 0 else if i = 8 then 32 else 36) →
      i = 6 ∨ i = 8 ∨ i = 9 → mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j = fsC mw SV F degree k i h := by
    intro j i h hj hi
    apply Fin.ext; rw [hOCv, hj]; simp; rcases hi with rfl | rfl | rfl <;> simp <;> omega
  have o1DD : σ1.st (fsC mw SV F degree k 6 (by decide)) = PCPPNative.descriptor c := by
    rw [← mO 0 6 (by decide) rfl (by simp), hσ1, updS_st_slot _ _ _ _ injO]; exact ho0
  have o1SZ : σ1.st (fsC mw SV F degree k 8 (by decide)) = List.replicate c.size true := by
    rw [← mO 32 8 (by decide) rfl (by simp), hσ1, updS_st_slot _ _ _ _ injO]; exact ho32
  have o1QC : σ1.st (fsC mw SV F degree k 9 (by decide)) = List.replicate q true := by
    rw [← mO 36 9 (by decide) rfl (by simp), hσ1, updS_st_slot _ _ _ _ injO]; exact ho36
  have o1sh : ∀ i, σ1.sh i = σ.sh i ∨ σ1.sh i = 0 := fun i => by
    rw [hσ1, updS_sh_zero _ injO]; split_ifs <;> simp
  have nO : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 17 + 11 * k.val → i.val ≠ 19 + 11 * k.val →
      i.val ≠ 20 + 11 * k.val →
      (i.val < bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k ∨
        bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k + 40 ≤ i.val) →
      ∀ j, mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k j ≠ i := fun i h1 h2 h3 h4 j e => by
    have hv := congrArg Fin.val e; rw [hOCv] at hv; have := j.isLt; split_ifs at hv <;> omega
  -- the cap
  obtain ⟨o2, hr2, -, -, ho2⟩ := CloseoutWitness.OracleCap.cap_run degree q c.size
  have hCv := mCAP_val (progB mw SV) (progU mw SV) (Dc degree) F k
  have hbC : 33 ≤ bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k := by unfold bCAP; omega
  have hbOC : bOC (progB mw SV).tapeCount (progU mw SV).tapeCount k + 40 ≤
      bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) 0 := by unfold bOC bCAP; simp; omega
  have hCC : bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) 0 ≤
      bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k := by unfold bCAP; simp
  have e2 := mach_ready cap hr2 (mCAP_inj (progB mw SV) (progU mw SV) (Dc degree) F k) σ1 (by
      intro j
      have hv := hCv j
      have hj : j.val < tCap (Dc degree) := j.isLt
      rw [hσ1, updS_sh_zero _ injO]; split_ifs with hex
      · rfl
      by_cases j0 : j.val = 0
      · have he : mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j = fsC mw SV F degree k 9 (by decide) :=
          Fin.ext (by rw [hv, if_pos j0]; simp; omega)
        rw [he]; exact (hfresh 9 (by decide) (by decide)).2
      by_cases j1 : j.val = 1
      · have he : mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j = fsC mw SV F degree k 8 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_pos j1]; simp; omega)
        rw [he]; exact (hfresh 8 (by decide) (by decide)).2
      by_cases jf : j.val = CloseoutWitness.OracleCap.Core.P (Dc degree) + 4
      · have he : mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j = fsC mw SV F degree k 10 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_neg j1, if_pos jf]; simp; omega)
        rw [he]; exact (hfresh 10 (by decide) (by decide)).2
      exact (hCAP _ (by rw [hv]; simp [j0, j1, jf]) (by rw [hv]; simp [j0, j1, jf])).2)
    (by
      intro j
      have hv := hCv j
      have hj : j.val < tCap (Dc degree) := j.isLt
      unfold CloseoutWitness.OracleCap.Core.input
      by_cases j0 : j.val = 0
      · have he : mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j = fsC mw SV F degree k 9 (by decide) :=
          Fin.ext (by rw [hv, if_pos j0]; simp; omega)
        rw [he, if_pos j0]; exact o1QC
      rw [if_neg j0]
      by_cases j1 : j.val = 1
      · have he : mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j = fsC mw SV F degree k 8 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_pos j1]; simp; omega)
        rw [he, if_pos j1]; exact o1SZ
      rw [if_neg j1]
      have hout : ∀ jj, mOC (progB mw SV) (progU mw SV) (tCap (Dc degree)) F k jj ≠
          mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j := by
        intro jj e
        have h1 := congrArg Fin.val e
        rw [hOCv, hv] at h1
        have := jj.isLt
        split_ifs at h1 <;> omega
      rw [hσ1, updS_st_other _ _ _ _ _ hout]
      by_cases jf : j.val = CloseoutWitness.OracleCap.Core.P (Dc degree) + 4
      · have he : mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j = fsC mw SV F degree k 10 (by decide) :=
          Fin.ext (by rw [hv, if_neg j0, if_neg j1, if_pos jf]; simp; omega)
        rw [he]; exact (hfresh 10 (by decide) (by decide)).1
      exact (hCAP _ (by rw [hv]; simp [j0, j1, jf]) (by rw [hv]; simp [j0, j1, jf])).1)
  set σ2 := updS (mCAP (progB mw SV) (progU mw SV) (Dc degree) F k) σ1 (fun _ => 0) o2 with hσ2
  have injC := mCAP_inj (progB mw SV) (progU mw SV) (Dc degree) F k
  have nC : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 19 + 11 * k.val → i.val ≠ 20 + 11 * k.val →
      i.val ≠ 21 + 11 * k.val →
      (i.val < bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k ∨
        bCAP (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) k + tCap (Dc degree) ≤ i.val) →
      ∀ j, mCAP (progB mw SV) (progU mw SV) (Dc degree) F k j ≠ i := fun i h1 h2 h3 h4 j e => by
    have hv := congrArg Fin.val e; rw [hCv] at hv; have : j.val < tCap (Dc degree) := j.isLt; split_ifs at hv <;> omega
  have hCF : mCAP (progB mw SV) (progU mw SV) (Dc degree) F k (CloseoutWitness.OracleCap.Core.flagSlot (Dc degree)) =
      fsC mw SV F degree k 10 (by decide) := by
    apply Fin.ext
    have hfv : (CloseoutWitness.OracleCap.Core.flagSlot (Dc degree)).val = CloseoutWitness.OracleCap.Core.P (Dc degree) + 4 :=
      CloseoutWitness.OracleCap.Core.compare_val (Dc degree) 2
    rw [hCv, hfv]; simp; omega
  refine ⟨σ2, WXExec.seq e1 e2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hCF, hσ2, updS_st_slot _ _ _ _ injC]; exact ho2
  · rw [← hCF, hσ2, updS_sh_slot _ _ _ _ injC]
  · rw [hσ2, updS_st_other _ _ _ _ _ (nC _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega))]; exact o1DD
  · rw [hσ2, updS_sh_other _ _ _ _ _ (nC _ (by simp; omega) (by simp; omega) (by simp; omega) (by simp; omega)), hσ1,
      updS_sh_zero _ injO]
    split_ifs <;> first | rfl | exact hDDh
  · intro i h1 h2 h3
    rw [hσ2, updS_st_other _ _ _ _ _ (nC i (by omega) (by omega) (by omega) h3),
      updS_sh_other _ _ _ _ _ (nC i (by omega) (by omega) (by omega) h3), hσ1,
      updS_st_other _ _ _ _ _ (nO i (by omega) (by omega) (by omega) h2),
      updS_sh_other _ _ _ _ _ (nO i (by omega) (by omega) (by omega) h2)]
    exact ⟨rfl, rfl⟩
  · rfl
  · rfl

theorem frontPart_exec (ν : ℕ) (hν : 1 ≤ ν) (hon : F.onset ≤ ν) (z : BitInput (2 ^ ν))
    (B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν))) (cap : ℕ) (σ : WState (NSC mw SV F degree) nrW)
    (hX : σ.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn z)) (hXh : σ.sh (cX _ _ _ _) = 0)
    (hXF : σ.st (cXF _ _ _ _) = []) (hXFh : σ.sh (cXF _ _ _ _) = 0)
    (hD0 : σ.st (fsC mw SV F degree 0 6 (by decide)) = PCPPNative.descriptor B.src)
    (hD0h : σ.sh (fsC mw SV F degree 0 6 (by decide)) = 0)
    (hD1 : σ.st (fsC mw SV F degree 1 6 (by decide)) = PCPPNative.descriptor B.pf)
    (hD1h : σ.sh (fsC mw SV F degree 1 6 (by decide)) = 0)
    (hFL : σ.st (cFL _ _ _ _) = [false]) (hFLh : σ.sh (cFL _ _ _ _) = 0)
    (hblk : ∀ i : Fin (NSC mw SV F degree + 1), bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) ≤ i.val →
      σ.st i = [] ∧ σ.sh i = 0)
    (hz : ∀ r ∈ [rOP, rT, rD], σ.val r = 0) (hcap : 4 * 2 ^ ν + 4 ≤ cap) :
    ∃ τ, WXExec cap (frontPart mw SV F degree) σ τ
        ((22 * 2 ^ ν + 1 + 1 + 7 + 1 + (18 * (2 * 2 ^ ν + 1) + 3 + 1 + (5 * (2 * 2 ^ ν + 1) + 1 + 1 +
          (5 * (2 * 2 ^ ν + 1) + 1)))) + 1 + (F.K * (2 ^ ν + 1) ^ 2 * ((PCPPNative.descriptor B.src).length +
          (PCPPNative.descriptor B.pf).length + Outer.width mw SV (2 ^ ν) + 1) ^ F.e + 1 + 2)) ∧
      τ.st (cFL _ _ _ _) = [decide (Guard G0 ν z B)] ∧
      (Guard G0 ν z B →
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.field) =
          RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.sizeSlot) =
          List.replicate (Outer.Dat mw SV ν B).D.size true ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.aritySlot) =
          List.replicate (Outer.width mw SV (2 ^ ν)) true) ∧
      (∀ j, τ.sh (mF (progB mw SV) (progU mw SV) (Dc degree) F j) = 0) ∧
      (∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 4 → i.val ≠ 10 → i.val ≠ 17 → i.val ≠ 28 →
        i.val < bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) →
        τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      τ.sh (cFL _ _ _ _) = 0 ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
  classical
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zO, zT, zD⟩ := hz
  have hzl : (List.ofFn z).length = 2 ^ ν := List.length_ofFn
  have e1 := Codec.copyRW_spec cap (cX _ _ _ _) (cXF _ _ _ _) (by simp [Fin.ext_iff]) rOP rT rD (by decide) (by decide)
    (by decide) (List.ofFn z) [] σ (by rw [hX, List.append_nil]) hXh hXF hXFh zO zT zD (by omega)
  set σ1 := σ.sets (cXF _ _ _ _) (RepairOrdinary.frame (List.ofFn z)) with hσ1
  obtain ⟨out, hr, hflag, hgood⟩ := F.run ν z B hν hon
  have hFv := mF_val (progB mw SV) (progU mw SV) (Dc degree) F
  have nd := F.inputs_nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  obtain ⟨⟨zs, zp⟩, sp⟩ := nd
  have hbF : 33 ≤ bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) := by unfold bF; omega
  have e2 := mach_ready cap hr (mF_inj (progB mw SV) (progU mw SV) (Dc degree) F) σ1 (by
      intro j
      have hv := hFv j
      rw [hσ1, WState.sets_sh]
      by_cases j1 : j = F.zIn
      · have he : mF (progB mw SV) (progU mw SV) (Dc degree) F j = cXF _ _ _ _ := Fin.ext (by rw [hv, if_pos j1]; rfl)
        rw [he]; exact hXFh
      by_cases j2 : j = F.sIn
      · have he : mF (progB mw SV) (progU mw SV) (Dc degree) F j = fsC mw SV F degree 0 6 (by decide) :=
          Fin.ext (by rw [hv, if_neg j1, if_pos j2]; rfl)
        rw [he]; exact hD0h
      by_cases j3 : j = F.pIn
      · have he : mF (progB mw SV) (progU mw SV) (Dc degree) F j = fsC mw SV F degree 1 6 (by decide) :=
          Fin.ext (by rw [hv, if_neg j1, if_neg j2, if_pos j3]; rfl)
        rw [he]; exact hD1h
      exact (hblk _ (by rw [hv, if_neg j1, if_neg j2, if_neg j3]; omega)).2)
    (by
      intro j
      have hv := hFv j
      unfold frontBank
      by_cases j1 : j = F.zIn
      · have he : mF (progB mw SV) (progU mw SV) (Dc degree) F j = cXF _ _ _ _ := Fin.ext (by rw [hv, if_pos j1]; rfl)
        rw [he, if_pos j1, hσ1, WState.sets_st, Function.update_self]
      rw [if_neg j1]
      by_cases j2 : j = F.sIn
      · have he : mF (progB mw SV) (progU mw SV) (Dc degree) F j = fsC mw SV F degree 0 6 (by decide) :=
          Fin.ext (by rw [hv, if_neg j1, if_pos j2]; rfl)
        rw [he, if_pos j2, hσ1, WState.sets_st, Function.update_of_ne (by simp [Fin.ext_iff]), hD0]
      rw [if_neg j2]
      by_cases j3 : j = F.pIn
      · have he : mF (progB mw SV) (progU mw SV) (Dc degree) F j = fsC mw SV F degree 1 6 (by decide) :=
          Fin.ext (by rw [hv, if_neg j1, if_neg j2, if_pos j3]; rfl)
        rw [he, if_pos j3, hσ1, WState.sets_st, Function.update_of_ne (by simp [Fin.ext_iff]), hD1]
      rw [if_neg j3, hσ1, WState.sets_st, Function.update_of_ne (fun e => by
        have := congrArg Fin.val e; rw [hv, if_neg j1, if_neg j2, if_neg j3] at this; simp at this; omega)]
      exact (hblk _ (by rw [hv, if_neg j1, if_neg j2, if_neg j3]; omega)).1)
  set σ2 := updS (mF (progB mw SV) (progU mw SV) (Dc degree) F) σ1 (fun _ => 0) out with hσ2
  have injF := mF_inj (progB mw SV) (progU mw SV) (Dc degree) F
  have nF : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 10 → i.val ≠ 17 → i.val ≠ 28 →
      i.val < bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) →
      ∀ j, mF (progB mw SV) (progU mw SV) (Dc degree) F j ≠ i := fun i h1 h2 h3 h4 j e => by
    have hv := congrArg Fin.val e; rw [hFv] at hv; split_ifs at hv <;> omega
  have FL2 : σ2.st (cFL _ _ _ _) = [false] := by
    rw [hσ2, updS_st_other _ _ _ _ _ (nF _ (by simp) (by simp) (by simp) (by simp; omega)), hσ1, WState.sets_st,
      Function.update_of_ne (by simp [Fin.ext_iff]), hFL]
  have FL2h : σ2.sh (cFL _ _ _ _) = 0 := by
    rw [hσ2, updS_sh_other _ _ _ _ _ (nF _ (by simp) (by simp) (by simp) (by simp; omega)), hσ1, WState.sets_sh, hFLh]
  have flag2 : σ2.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.flag) = [decide (Guard G0 ν z B)] := by
    rw [hσ2, updS_st_slot _ _ _ _ injF, hflag]
  have hw : wbit σ2 (mF (progB mw SV) (progU mw SV) (Dc degree) F F.flag) = decide (Guard G0 ν z B) := by
    unfold wbit; rw [flag2, hσ2, updS_sh_slot _ _ _ _ injF]; rfl
  have hne4 : ∀ j, mF (progB mw SV) (progU mw SV) (Dc degree) F j ≠ cFL _ _ _ _ :=
    nF _ (by simp) (by simp) (by simp) (by simp; omega)
  have common : ∀ τ : WState (NSC mw SV F degree) nrW, (τ = σ2 ∨ τ = σ2.sets (cFL _ _ _ _) [true]) →
      (∀ j, τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F j) = out j) ∧
      (∀ j, τ.sh (mF (progB mw SV) (progU mw SV) (Dc degree) F j) = 0) ∧
      (∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 4 → i.val ≠ 10 → i.val ≠ 17 → i.val ≠ 28 →
        i.val < bF (progB mw SV).tapeCount (progU mw SV).tapeCount (tCap (Dc degree)) →
        τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧ τ.sh (cFL _ _ _ _) = 0 ∧ τ.val = σ.val ∧ τ.cell = σ.cell := by
    intro τ hτ
    have base : ∀ i, i ≠ cFL _ _ _ _ → τ.st i = σ2.st i ∧ τ.sh i = σ2.sh i := fun i hi => by
      rcases hτ with rfl | rfl
      · exact ⟨rfl, rfl⟩
      · simp [Function.update_of_ne hi]
    refine ⟨fun j => ?_, fun j => ?_, fun i h4 h10 h17 h28 hb => ?_, ?_, ?_, ?_⟩
    · rw [(base _ (hne4 j)).1, hσ2, updS_st_slot _ _ _ _ injF]
    · rw [(base _ (hne4 j)).2, hσ2, updS_sh_slot _ _ _ _ injF]
    · rw [(base i (fun e => h4 (by rw [e]; rfl))).1, (base i (fun e => h4 (by rw [e]; rfl))).2, hσ2,
        updS_st_other _ _ _ _ _ (nF i h10 h17 h28 hb), updS_sh_other _ _ _ _ _ (nF i h10 h17 h28 hb), hσ1,
        WState.sets_st, WState.sets_sh, Function.update_of_ne (fun e => h10 (by rw [e]; rfl))]
      exact ⟨rfl, rfl⟩
    · rcases hτ with rfl | rfl
      · exact FL2h
      · simpa using FL2h
    · rcases hτ with rfl | rfl <;> simp [hσ2, hσ1]
    · rcases hτ with rfl | rfl <;> simp [hσ2, hσ1]
  by_cases hg : Guard G0 ν z B
  · have e3 : WXExec cap (.ifs (mF (progB mw SV) (progU mw SV) (Dc degree) F F.flag) (WMX.wr (cFL _ _ _ _) true)
        WMX.skip) σ2 (σ2.sets (cFL _ _ _ _) [true]) 2 := by
      have := WXExec.ifsT (Q := WMX.skip) (by rw [hw]; simp [hg]) (WXExec.wr (cap := cap) (cFL _ _ _ _) true σ2)
      refine WXExec.cast cap this ?_ (by omega)
      rw [FL2, FL2h]; rfl
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := common _ (Or.inr rfl)
    obtain ⟨g1, g2, g3⟩ := hgood hg
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 e3)) (by simp only [hzl]; omega), ?_,
      fun _ => ⟨by rw [c1, g1], by rw [c1, g2], by rw [c1, g3]⟩, c2, c3, c4, c5, c6⟩
    simp [decide_eq_true hg]
  · have e3 : WXExec cap (.ifs (mF (progB mw SV) (progU mw SV) (Dc degree) F F.flag) (WMX.wr (cFL _ _ _ _) true)
        WMX.skip) σ2 σ2 1 :=
      WXExec.ifsF (P := WMX.wr (cFL _ _ _ _) true) (by rw [hw]; simp [hg]) (WXExec.skip cap σ2)
    obtain ⟨c1, c2, c3, c4, c5, c6⟩ := common _ (Or.inl rfl)
    refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 e3)) (by simp only [hzl]; omega), ?_,
      fun h => absurd h hg, c2, c3, c4, c5, c6⟩
    rw [FL2, decide_eq_false hg]

end Cap

end W3.NearCubicWires.RepairSource.Outer3.Front
