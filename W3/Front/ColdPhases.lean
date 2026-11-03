import W3.Front.ColdField

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)
open NearCubicWires.RepairOrdinary.RadixSemantics (value)

namespace W3.NearCubicWires.RepairSource.Outer3.Front

/-- The padded guess word is gates' `guessWord` with phase B's padding. -/
theorem prefixBits_guess (n : ℕ) (raw : List Bool) (h : 16 * raw.length ≤ n) :
    Codec.prefixBits raw (4 * (n / 16) + 5) = guessWord n raw (padB n (n / 16 + 1)) := by
  unfold guessWord padB
  rw [prefixBits_eq, prefixBits_eq, List.take_of_length_le (by omega), List.take_of_length_le (by omega),
    List.append_assoc, List.replicate_append_replicate]
  congr 2
  omega

section W
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

theorem wtP_exec (n : ℕ) (raw : List Bool) (cap : ℕ) (σ : WState (NSC mw SV F degree) nrW)
    (hRAW : σ.st (cRAW _ _ _ _) = RepairOrdinary.frame raw) (hRAWh : σ.sh (cRAW _ _ _ _) = 0)
    (hWT : σ.st (cWT _ _ _ _) = []) (hWTh : σ.sh (cWT _ _ _ _) = 0)
    (hN : σ.val rN = n) (hz : ∀ r ∈ [kQ, hH, hBr, rW, dS, oW], σ.val r = 0) (hcap : 8 * n + 100 ≤ cap) :
    ∃ τ, WXExec cap (wtP mw SV F degree) σ τ (200 * (n + 1) + 18 * (4 * (n / 16) + 5) + 100) ∧
      τ.st (cWT _ _ _ _) = Codec.prefixBits raw (4 * (n / 16) + 5) ∧ τ.sh (cWT _ _ _ _) = 0 ∧
      (∀ i, i ≠ cWT _ _ _ _ → i ≠ cRAW _ _ _ _ → τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      τ.val = Function.update σ.val kQ (n / 16) ∧ τ.cell = σ.cell := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zQ, zH, zB, zW, zS, zO⟩ := hz
  set m := 4 * (n / 16) + 5 with hm
  have e1 := Codec.dupR_spec cap rN kQ dS (by decide) (by decide) (by decide) σ zS (by rw [hN, zQ]; omega)
  rw [zQ, hN, Nat.zero_add] at e1
  set σ1 := σ.setv kQ n with hσ1
  have e2 := div16_exec (cap := cap) (X := kQ) (H := hH) (B := hBr) (by decide) (by decide) (by decide) σ1 n
    (by simp [hσ1]) (by rw [hσ1, WState.setv_val, Function.update_of_ne (by decide)]; exact zH)
    (by rw [hσ1, WState.setv_val, Function.update_of_ne (by decide)]; exact zB) (by omega)
  set σ2 := σ1.setv kQ (n / 16) with hσ2
  have hdup : ∀ (τ : WState (NSC mw SV F degree) nrW) (w : ℕ), τ.val kQ = n / 16 → τ.val dS = 0 → τ.val rW = w →
      w + n / 16 ≤ cap → WExec cap (Codec.dupR kQ rW dS) τ (τ.setv rW (w + n / 16)) (18 * (n / 16) + 3) := by
    intro τ w h1 h2 h3 h4
    have := Codec.dupR_spec cap kQ rW dS (by decide) (by decide) (by decide) τ h2 (by rw [h1, h3]; omega)
    rwa [h1, h3] at this
  have v2 : ∀ r, r ≠ kQ → σ2.val r = σ.val r := fun r hr => by simp [hσ2, hσ1, Function.update_of_ne hr]
  have e3 := hdup σ2 0 (by simp [hσ2]) (by rw [v2 _ (by decide)]; exact zS) (by rw [v2 _ (by decide)]; exact zW)
    (by omega)
  have e4 := hdup (σ2.setv rW (0 + n / 16)) (n / 16) (by simp (config := { decide := true }) [hσ2, Function.update_apply, rW, kQ])
    (by simp (config := { decide := true }) [Function.update_apply, rW, dS]; rw [v2 _ (by decide)]; exact zS) (by simp) (by omega)
  have e5 := hdup ((σ2.setv rW (0 + n / 16)).setv rW (n / 16 + n / 16)) (n / 16 + n / 16)
    (by simp (config := { decide := true }) [hσ2, Function.update_apply, rW, kQ]) (by simp (config := { decide := true }) [Function.update_apply, rW, dS]; rw [v2 _ (by decide)]; exact zS)
    (by simp) (by omega)
  have e6 := hdup (((σ2.setv rW (0 + n / 16)).setv rW (n / 16 + n / 16)).setv rW (n / 16 + n / 16 + n / 16))
    (n / 16 + n / 16 + n / 16)
    (by simp (config := { decide := true }) [hσ2, Function.update_apply, rW, kQ]) (by simp (config := { decide := true }) [Function.update_apply, rW, dS]; rw [v2 _ (by decide)]; exact zS)
    (by simp) (by omega)
  set σ6 := σ2.setv rW (4 * (n / 16)) with hσ6
  have h6eq : ((((σ2.setv rW (0 + n / 16)).setv rW (n / 16 + n / 16)).setv rW (n / 16 + n / 16 + n / 16)).setv rW
      (n / 16 + n / 16 + n / 16 + n / 16)) = σ6 := by
    rw [hσ6]; simp only [LitDecode.setv_setv]; congr 1; omega
  rw [h6eq] at e6
  have e7 := NodeEmit.incN_spec (cap := cap) rW 5 σ6 (by simp [hσ6]; omega)
  rw [show σ6.setv rW (σ6.val rW + 5) = σ2.setv rW m by rw [hσ6]; simp [LitDecode.setv_setv, hm]] at e7
  set σ7 := σ2.setv rW m with hσ7
  have e8 := Codec.unframeW_spec cap (cRAW _ _ _ _) (cWT _ _ _ _) (by simp [Fin.ext_iff]) oW rW (by decide) raw m σ7
    (by simp [hσ7, hσ2, hσ1, hRAW]) (by simp [hσ7, hσ2, hσ1, hRAWh]) (by simp [hσ7, hσ2, hσ1, hWT, hWTh])
    (by simp [hσ7]) (by omega)
    (by simp (config := { decide := true }) [hσ7, hσ2, hσ1, Function.update_apply, oW, rW, kQ]; rw [zO]; omega)
  set σ8 := ((NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO σ7 (cWT _ _ _ _) oW
    (Codec.prefixBits raw m)).seth (cRAW _ _ _ _) (2 * min m raw.length)).setv rW 0 with hσ8
  have hpl : (Codec.prefixBits raw m).length = m := by simp only [Codec.prefixBits, List.length_ofFn]
  have v8 : σ8.val oW = m := by
    simp (config := { decide := true }) [hσ8, hσ7, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO,
      Function.update_apply, oW, rW, kQ, zO, hpl]
  have e9 := wrewind_spec cap (cWT _ _ _ _) oW m σ8 v8 (by rw [v8]; omega)
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq (WXExec.wm e3)
    (WXExec.seq (WXExec.wm e4) (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7)
      (WXExec.seq (WXExec.wm e8) (WXExec.wm e9))))))))) ?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · simp [hσ8, hσ7, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hWT]
  · simp [hσ8, hσ7, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, hWTh, hpl, Fin.ext_iff]
  · intro i h1 h2
    simp [hσ8, hσ7, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, Function.update_of_ne h1,
      Function.update_of_ne h2]
  · funext r
    simp only [hσ8, hσ7, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO, WState.setv_val,
      WState.seth_val, WState.sets_val, Function.update_apply]
    by_cases r1 : r = oW
    · subst r1; simp (config := { decide := true }) [zO]
    by_cases r2 : r = rW
    · subst r2; simp (config := { decide := true }) [zW]
    by_cases r3 : r = kQ
    · subst r3; simp (config := { decide := true })
    simp [r1, r2, r3]
  · simp [hσ8, hσ7, hσ2, hσ1, NearCubicWires.WireExponent3_5.PrimAsm.WriteNat.appendO]

end W

section Wd
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

noncomputable abbrev wuOut := mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F (progU mw SV).outputTape

theorem mWB_val (j : Fin (progB mw SV).tapeCount) :
    (mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j).val = if j.val = 0 then 8 else 33 + j.val := by
  unfold mWB; split_ifs <;> rfl

theorem mWU_val (j : Fin (progU mw SV).tapeCount) :
    (mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j).val =
      if j.val = 0 then 9 else 33 + (progB mw SV).tapeCount + j.val := by
  unfold mWU; split_ifs <;> rfl

theorem mWB_inj : Function.Injective (mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F) := by
  intro i j h; have hv := congrArg Fin.val h; rw [mWB_val, mWB_val] at hv; apply Fin.ext; split_ifs at hv <;> omega

theorem mWU_inj : Function.Injective (mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F) := by
  intro i j h; have hv := congrArg Fin.val h; rw [mWU_val, mWU_val] at hv; apply Fin.ext; split_ifs at hv <;> omega

def widthCost (n q K : ℕ) : ℕ := 2 * (100 * n + 100) + 2 * (2 * (K * (n + 1) ^ 1) + 2) + 100 * (q + 1) + 20

theorem widthP_exec {n : ℕ} (x : BitInput n) (cap : ℕ) (σ : WState (NSC mw SV F degree) nrW)
    (hX : σ.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn x)) (hXh : σ.sh (cX _ _ _ _) = 0)
    (hW1 : σ.st (cXW1 _ _ _ _) = []) (hW1h : σ.sh (cXW1 _ _ _ _) = 0)
    (hW2 : σ.st (cXW2 _ _ _ _) = []) (hW2h : σ.sh (cXW2 _ _ _ _) = 0)
    (hblk : ∀ i : Fin (NSC mw SV F degree + 1), 33 ≤ i.val →
      i.val < 33 + (progB mw SV).tapeCount + (progU mw SV).tapeCount → σ.st i = [] ∧ σ.sh i = 0)
    (hz : ∀ r ∈ [rOP, rT, rD, rQ], σ.val r = 0) (hcap : 8 * n + 4 * OuterM.qOf mw SV n + 20 ≤ cap) :
    ∃ τ, WXExec cap (widthP mw SV F degree) σ τ (widthCost n (OuterM.qOf mw SV n) (OuterM.widthDonor mw SV).K) ∧
      τ.st (wbOut mw SV F degree) = RepairOrdinary.frame (OuterM.qOf mw SV n).bits ∧
      τ.sh (wbOut mw SV F degree) = 0 ∧ τ.val rQ = OuterM.qOf mw SV n ∧
      (∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 8 → i.val ≠ 9 →
        (i.val < 33 ∨ 33 + (progB mw SV).tapeCount + (progU mw SV).tapeCount ≤ i.val) →
        τ.st i = σ.st i ∧ τ.sh i = σ.sh i) ∧
      (∀ r, r ≠ rQ → τ.val r = σ.val r) ∧ τ.cell = σ.cell := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨zOP, zT, zD, zQ⟩ := hz
  set q := OuterM.qOf mw SV n with hq
  have hxl : (List.ofFn x).length = n := List.length_ofFn
  -- 1. copy `frame x`
  have e1 := Codec.copyRW_spec cap (cX _ _ _ _) (cXW1 _ _ _ _) (by simp [Fin.ext_iff]) rOP rT rD (by decide)
    (by decide) (by decide) (List.ofFn x) [] σ (by rw [hX, List.append_nil]) hXh hW1 hW1h zOP zT zD (by omega)
  set σ1 := σ.sets (cXW1 _ _ _ _) (RepairOrdinary.frame (List.ofFn x)) with hσ1

  obtain ⟨outB, hrB, hoB⟩ := CheckedPCPP.wordFunction_ready (OuterM.widthDonor mw SV).word ⟨n, x⟩
  have eB := mach_ready cap hrB (mWB_inj mw SV F degree) σ1 (by
      intro j
      have hv := mWB_val mw SV F degree j
      by_cases j0 : j.val = 0
      · have he : mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j = cXW1 _ _ _ _ := Fin.ext (by
          rw [hv, if_pos j0]; rfl)
        rw [he, hσ1, WState.sets_sh]; exact hW1h
      · rw [hσ1, WState.sets_sh]
        have hj : j.val < (progB mw SV).tapeCount := j.isLt
        exact (hblk _ (by rw [hv, if_neg j0]; omega) (by rw [hv, if_neg j0]; omega)).2)
    (by
      intro j
      rw [CheckedPCPP.program_inputTapes]
      have hv := mWB_val mw SV F degree j
      by_cases j0 : j.val = 0
      · have he : mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j = cXW1 _ _ _ _ := Fin.ext (by
          rw [hv, if_pos j0]; rfl)
        rw [he, if_pos j0, hσ1, WState.sets_st, Function.update_self]
      · rw [if_neg j0, hσ1, WState.sets_st, Function.update_of_ne (fun e => by
          have := congrArg Fin.val e; rw [hv, if_neg j0] at this; simp at this; omega)]
        have hj : j.val < (progB mw SV).tapeCount := j.isLt
        exact (hblk _ (by rw [hv, if_neg j0]; omega) (by rw [hv, if_neg j0]; omega)).1)
  set σ2 := updS (mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F) σ1 (fun _ => 0) outB with hσ2
  have nB : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 8 → (i.val < 33 ∨ 33 + (progB mw SV).tapeCount ≤ i.val) →
      ∀ j, mWB (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j ≠ i := fun i h1 h2 j e => by
    have hv := congrArg Fin.val e; rw [mWB_val] at hv; have hj : j.val < (progB mw SV).tapeCount := j.isLt
    split_ifs at hv <;> omega
  have st2 : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 8 → (i.val < 33 ∨ 33 + (progB mw SV).tapeCount ≤ i.val) →
      σ2.st i = σ.st i ∧ σ2.sh i = σ.sh i := fun i h1 h2 => by
    rw [hσ2, updS_st_other _ _ _ _ i (nB i h1 h2), updS_sh_other _ _ _ _ i (nB i h1 h2), hσ1, WState.sets_st,
      WState.sets_sh, Function.update_of_ne (fun e => h1 (by rw [e]; rfl))]
    exact ⟨rfl, rfl⟩
  have wb2 : σ2.st (wbOut mw SV F degree) = RepairOrdinary.frame q.bits := by
    rw [hσ2, updS_st_slot _ _ _ _ (mWB_inj mw SV F degree), hoB]
  have wb2h : σ2.sh (wbOut mw SV F degree) = 0 := by
    rw [hσ2, updS_sh_slot _ _ _ _ (mWB_inj mw SV F degree)]
  -- 3. copy `frame x` again
  have e3 := Codec.copyRW_spec cap (cX _ _ _ _) (cXW2 _ _ _ _) (by simp [Fin.ext_iff]) rOP rT rD (by decide)
    (by decide) (by decide) (List.ofFn x) [] σ2
    (by rw [(st2 _ (by simp) (by simp)).1, hX, List.append_nil]) (by rw [(st2 _ (by simp) (by simp)).2, hXh])
    (by rw [(st2 _ (by simp) (by simp)).1, hW2]) (by rw [(st2 _ (by simp) (by simp)).2, hW2h])
    (by simp [hσ2, hσ1, zOP]) (by simp [hσ2, hσ1, zT]) (by simp [hσ2, hσ1, zD]) (by omega)
  set σ3 := σ2.sets (cXW2 _ _ _ _) (RepairOrdinary.frame (List.ofFn x)) with hσ3

  obtain ⟨outU, hrU, hoU⟩ := CheckedPCPP.wordFunction_ready (OuterM.widthDonor mw SV).unary ⟨n, x⟩
  have eU := mach_ready cap hrU (mWU_inj mw SV F degree) σ3 (by
      intro j
      have hv := mWU_val mw SV F degree j
      by_cases j0 : j.val = 0
      · have he : mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j = cXW2 _ _ _ _ := Fin.ext (by
          rw [hv, if_pos j0]; rfl)
        rw [he, hσ3, WState.sets_sh, (st2 _ (by simp) (by simp)).2]; exact hW2h
      · have hj : j.val < (progU mw SV).tapeCount := j.isLt
        rw [hσ3, WState.sets_sh, (st2 _ (by rw [hv, if_neg j0]; omega) (by rw [hv, if_neg j0]; omega)).2]
        exact (hblk _ (by rw [hv, if_neg j0]; omega) (by rw [hv, if_neg j0]; omega)).2)
    (by
      intro j
      rw [CheckedPCPP.program_inputTapes]
      have hv := mWU_val mw SV F degree j
      by_cases j0 : j.val = 0
      · have he : mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j = cXW2 _ _ _ _ := Fin.ext (by
          rw [hv, if_pos j0]; rfl)
        rw [he, if_pos j0, hσ3, WState.sets_st, Function.update_self]
      · have hj : j.val < (progU mw SV).tapeCount := j.isLt
        rw [if_neg j0, hσ3, WState.sets_st, Function.update_of_ne (fun e => by
          have := congrArg Fin.val e; rw [hv, if_neg j0] at this; simp at this; omega),
          (st2 _ (by rw [hv, if_neg j0]; omega) (by rw [hv, if_neg j0]; omega)).1]
        exact (hblk _ (by rw [hv, if_neg j0]; omega) (by rw [hv, if_neg j0]; omega)).1)
  set σ4 := updS (mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F) σ3 (fun _ => 0) outU with hσ4
  -- 5. `rQ := q`
  have e5 := Codec.unaryQ_spec cap (wuOut mw SV F degree) rQ rT rD (by decide) (by decide) (by decide) q σ4
    (by rw [hσ4, updS_st_slot _ _ _ _ (mWU_inj mw SV F degree), hoU])
    (by rw [hσ4, updS_sh_slot _ _ _ _ (mWU_inj mw SV F degree)])
    (by simp [hσ4, hσ3, hσ2, hσ1, zQ]) (by simp [hσ4, hσ3, hσ2, hσ1, zT]) (by simp [hσ4, hσ3, hσ2, hσ1, zD])
    (by omega)
  have nU : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 9 →
      (i.val < 33 + (progB mw SV).tapeCount ∨ 33 + (progB mw SV).tapeCount + (progU mw SV).tapeCount ≤ i.val) →
      ∀ j, mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j ≠ i := fun i h1 h2 j e => by
    have hv := congrArg Fin.val e; rw [mWU_val] at hv; have hj : j.val < (progU mw SV).tapeCount := j.isLt
    split_ifs at hv <;> omega
  have hwbU : ∀ j, mWU (progB mw SV) (progU mw SV) (tCap (Dc degree)) F j ≠ wbOut mw SV F degree := by
    intro j e
    have hv := congrArg Fin.val e
    rw [mWU_val] at hv
    have hb : (wbOut mw SV F degree).val = 33 + (progB mw SV).outputTape.val := by
      have := (progB mw SV).outputFresh
      simp only [wbOut, mWB, if_neg this]; rfl
    have := (progB mw SV).outputTape.isLt
    rw [hb] at hv; split_ifs at hv <;> omega
  refine ⟨_, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq eB (WXExec.seq (WXExec.wm e3)
    (WXExec.seq eU (WXExec.wm e5))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold widthCost; simp only [hxl]; omega
  · rw [WState.setv_st, hσ4, updS_st_other _ _ _ _ _ hwbU, hσ3, WState.sets_st, Function.update_of_ne (fun e => by
      have := congrArg Fin.val e
      have hb : (wbOut mw SV F degree).val = 33 + (progB mw SV).outputTape.val := by
        have := (progB mw SV).outputFresh
        simp only [wbOut, mWB, if_neg this]; rfl
      rw [hb] at this; simp at this; omega), wb2]
  · rw [WState.setv_sh, hσ4, updS_sh_other _ _ _ _ _ hwbU, hσ3, WState.sets_sh, wb2h]
  · simp
  · intro i h8 h9 hb
    rw [WState.setv_st, WState.setv_sh, hσ4, updS_st_other _ _ _ _ _ (nU i h9 (by omega)),
      updS_sh_other _ _ _ _ _ (nU i h9 (by omega)), hσ3, WState.sets_st, WState.sets_sh,
      Function.update_of_ne (fun e => h9 (by rw [e]; rfl))]
    exact st2 i h8 (by omega)
  · intro r hr; simp [hσ4, hσ3, hσ2, hσ1, Function.update_of_ne hr]
  · simp [hσ4, hσ3, hσ2, hσ1]

end Wd

/-! ## The code bound -/

/-- `L(q) = 8192 ((q+1)^{E₀} + q + 5)^{10}` and `M(q) = 16 L(q) + q + 4`. -/
def Lq (E q : ℕ) : ℕ := 8192 * ((q + 1) ^ E + q + 5) ^ 10
def Mq (E q : ℕ) : ℕ := 16 * Lq E q + q + 4

def boundCost (E q : ℕ) : ℕ :=
  20 * (q + 1) + 20 + CheckedPCPP.EncSetup.powCost ((q + 1) ^ E) E + 20 * (q + 1) + 20 + 40000 +
    CheckedPCPP.EncSetup.powCost (Lq E q) 10 + 100 + CheckedPCPP.EncSetup.powCost (16 * Lq E q) 1 + 20 * (q + 1) + 40

section B
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

theorem boundP_exec (q cap : ℕ) (σ : WState (NSC mw SV F degree) nrW) (hQ : σ.val rQ = q)
    (hz : ∀ r ∈ [rQ1, rA, rL, rM, dS, pX3, pH, pB], σ.val r = 0)
    (hcap : 3 * (Mq (E0 degree) q * Mq (E0 degree) q) + 100 ≤ cap) :
    WXExec cap (boundP mw SV F degree) σ
      ((((σ.setv rQ1 (q + 1)).setv rA ((q + 1) ^ E0 degree + q + 5)).setv rL (Lq (E0 degree) q)).setv rM
        (Mq (E0 degree) q)) (boundCost (E0 degree) q) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hz
  obtain ⟨z1, zA, zL, zM, zS, zX3, zH, zB⟩ := hz
  set E := E0 degree with hE
  set P := (q + 1) ^ E + q + 5 with hP
  have hP1 : (q + 1) ^ E ≤ P := by omega
  have hq1 : 1 ≤ (q + 1) ^ E := Nat.one_le_pow _ _ (by omega)
  have hLq : Lq E q = 8192 * P ^ 10 := rfl
  have hPL : P ≤ P ^ 10 := Nat.le_self_pow (by norm_num) _
  have hM : Mq E q = 16 * Lq E q + q + 4 := rfl
  have hLM : Lq E q ≤ Mq E q := by omega
  have hPM : P ≤ Mq E q := by rw [hM, hLq]; omega
  have hMM : Mq E q ≤ Mq E q * Mq E q := Nat.le_mul_self _
  -- the steps
  have e1 := Codec.dupR_spec cap rQ rQ1 dS (by decide) (by decide) (by decide) σ zS (by rw [hQ, z1]; omega)
  rw [z1, hQ, Nat.zero_add] at e1
  have e2 := WXExec.inc (cap := cap) rQ1 (σ.setv rQ1 q) (by simp; omega)
  simp only [WState.setv_val, Function.update_self, LitDecode.setv_setv] at e2
  have e3 := WXExec.inc (cap := cap) rA (σ.setv rQ1 (q + 1)) (by
    simp only [WState.setv_val]; rw [Function.update_of_ne (by decide), zA]; omega)
  simp only [WState.setv_val, Function.update_of_ne (show rA ≠ rQ1 by decide), zA, Nat.zero_add] at e3
  set τ3 := (σ.setv rQ1 (q + 1)).setv rA 1 with hτ3
  have v3 : ∀ r, r ≠ rQ1 → r ≠ rA → τ3.val r = σ.val r := fun r h1 h2 => by
    simp (config := { decide := true }) [hτ3, Function.update_of_ne h1, Function.update_of_ne h2]
  have e4 := CheckedPCPP.EncSetup.powW_spec (cap := cap) (X := rQ1) (Y := rA) (Z := pX3) (A2 := pH) (T := pB)
    (by decide) ((q + 1) ^ E) E τ3 (by rw [v3 _ (by decide) (by decide)]; exact zX3)
    (by rw [v3 _ (by decide) (by decide)]; exact zH) (by rw [v3 _ (by decide) (by decide)]; exact zB)
    (by simp (config := { decide := true }) [hτ3, Function.update_apply]) (by simp (config := { decide := true }) [hτ3, Function.update_apply])
    (by nlinarith)
  rw [show τ3.setv rA (τ3.val rA * τ3.val rQ1 ^ E) = (σ.setv rQ1 (q + 1)).setv rA ((q + 1) ^ E) by
    simp (config := { decide := true }) [hτ3, LitDecode.setv_setv, Function.update_apply]] at e4
  set τ4 := (σ.setv rQ1 (q + 1)).setv rA ((q + 1) ^ E) with hτ4
  have v4 : ∀ r, r ≠ rQ1 → r ≠ rA → τ4.val r = σ.val r := fun r h1 h2 => by
    simp (config := { decide := true }) [hτ4, Function.update_of_ne h1, Function.update_of_ne h2]
  have e5 := Codec.dupR_spec cap rQ rA dS (by decide) (by decide) (by decide) τ4
    (by rw [v4 _ (by decide) (by decide)]; exact zS)
    (by rw [v4 rQ (by decide) (by decide)]; simp (config := { decide := true }) [hτ4]; omega)
  rw [v4 rQ (by decide) (by decide), hQ] at e5
  have e6 := NodeEmit.incN_spec (cap := cap) rA 5 (τ4.setv rA (τ4.val rA + q)) (by simp (config := { decide := true }) [hτ4]; omega)
  rw [show (τ4.setv rA (τ4.val rA + q)).setv rA ((τ4.setv rA (τ4.val rA + q)).val rA + 5) =
      (σ.setv rQ1 (q + 1)).setv rA P by simp (config := { decide := true }) [hτ4, LitDecode.setv_setv, hP]] at e6
  set τ6 := (σ.setv rQ1 (q + 1)).setv rA P with hτ6
  have v6 : ∀ r, r ≠ rQ1 → r ≠ rA → τ6.val r = σ.val r := fun r h1 h2 => by
    simp (config := { decide := true }) [hτ6, Function.update_of_ne h1, Function.update_of_ne h2]
  have e7 := NodeEmit.incN_spec (cap := cap) rL 8192 τ6 (by rw [v6 _ (by decide) (by decide), zL]; omega)
  rw [v6 rL (by decide) (by decide), zL, Nat.zero_add] at e7
  set τ7 := τ6.setv rL 8192 with hτ7
  have v7 : ∀ r, r ≠ rQ1 → r ≠ rA → r ≠ rL → τ7.val r = σ.val r := fun r h1 h2 h3 => by
    simp (config := { decide := true }) [hτ7, Function.update_of_ne h3]; exact v6 r h1 h2
  have e8 := CheckedPCPP.EncSetup.powW_spec (cap := cap) (X := rA) (Y := rL) (Z := pX3) (A2 := pH) (T := pB)
    (by decide) (Lq E q) 10 τ7 (by rw [v7 _ (by decide) (by decide) (by decide)]; exact zX3)
    (by rw [v7 _ (by decide) (by decide) (by decide)]; exact zH)
    (by rw [v7 _ (by decide) (by decide) (by decide)]; exact zB)
    (by simp (config := { decide := true }) [hτ7, hτ6, Function.update_apply, hLq])
    (by simp (config := { decide := true }) [hτ7, hτ6, Function.update_apply]; omega) (by nlinarith)
  rw [show τ7.setv rL (τ7.val rL * τ7.val rA ^ 10) = τ6.setv rL (Lq E q) by
    simp (config := { decide := true }) [hτ7, hτ6, LitDecode.setv_setv, Function.update_apply, hLq]] at e8
  set τ8 := τ6.setv rL (Lq E q) with hτ8
  have v8 : ∀ r, r ≠ rQ1 → r ≠ rA → r ≠ rL → τ8.val r = σ.val r := fun r h1 h2 h3 => by
    simp (config := { decide := true }) [hτ8, Function.update_of_ne h3]; exact v6 r h1 h2
  have e9 := NodeEmit.incN_spec (cap := cap) rM 16 τ8 (by rw [v8 _ (by decide) (by decide) (by decide), zM]; omega)
  rw [v8 rM (by decide) (by decide) (by decide), zM, Nat.zero_add] at e9
  set τ9 := τ8.setv rM 16 with hτ9
  have v9 : ∀ r, r ≠ rQ1 → r ≠ rA → r ≠ rL → r ≠ rM → τ9.val r = σ.val r := fun r h1 h2 h3 h4 => by
    simp (config := { decide := true }) [hτ9, Function.update_of_ne h4]; exact v8 r h1 h2 h3
  have e10 := CheckedPCPP.EncSetup.powW_spec (cap := cap) (X := rL) (Y := rM) (Z := pX3) (A2 := pH) (T := pB)
    (by decide) (16 * Lq E q) 1 τ9 (by rw [v9 _ (by decide) (by decide) (by decide) (by decide)]; exact zX3)
    (by rw [v9 _ (by decide) (by decide) (by decide) (by decide)]; exact zH)
    (by rw [v9 _ (by decide) (by decide) (by decide) (by decide)]; exact zB)
    (by simp (config := { decide := true }) [hτ9, hτ8, Function.update_apply])
    (by simp (config := { decide := true }) [hτ9, hτ8, Function.update_apply, hLq]
        have := Nat.one_le_pow 10 P (by omega); omega)
    (by nlinarith)
  rw [show τ9.setv rM (τ9.val rM * τ9.val rL ^ 1) = τ8.setv rM (16 * Lq E q) by
    simp (config := { decide := true }) [hτ9, hτ8, LitDecode.setv_setv, Function.update_apply]] at e10
  set τ10 := τ8.setv rM (16 * Lq E q) with hτ10
  have e11 := Codec.dupR_spec cap rQ rM dS (by decide) (by decide) (by decide) τ10
    (by simp (config := { decide := true }) [hτ10, hτ8, Function.update_apply]; rw [v6 _ (by decide) (by decide)]; exact zS)
    (by simp (config := { decide := true }) [hτ10, hτ8, Function.update_apply]; rw [v6 rQ (by decide) (by decide), hQ]; omega)
  have hτ10Q : τ10.val rQ = q := by simp (config := { decide := true }) [hτ10, hτ8, Function.update_apply]; rw [v6 rQ (by decide) (by decide), hQ]
  rw [hτ10Q] at e11
  have e12 := NodeEmit.incN_spec (cap := cap) rM 4 (τ10.setv rM (τ10.val rM + q)) (by simp (config := { decide := true }) [hτ10]; omega)
  refine WXExec.cast cap (WXExec.seq (WXExec.wm e1) (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq e4
    (WXExec.seq (WXExec.wm e5) (WXExec.seq (WXExec.wm e6) (WXExec.seq (WXExec.wm e7) (WXExec.seq e8
      (WXExec.seq (WXExec.wm e9) (WXExec.seq e10 (WXExec.seq (WXExec.wm e11) (WXExec.wm e12)))))))))))) ?_ ?_
  · simp (config := { decide := true }) [hτ10, hτ8, hτ6, LitDecode.setv_setv, Function.update_apply, hM]
  · unfold boundCost; omega

end B

end W3.NearCubicWires.RepairSource.Outer3.Front
