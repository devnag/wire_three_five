import W3.Front.Check

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

namespace W3.NearCubicWires.RepairSource.Outer3.Front

/-- The cold state: `frame z` on `Z`, the two descriptors on `S`, `Pf`. -/
def startF (ta th : ℕ) (z s p : List Bool) : WState (nsF ta th) nrW :=
  ⟨fun _ => 0, fun i => if i.val = 0 then RepairOrdinary.frame z else if i.val = 3 then s else if i.val = 5 then p
    else [], fun _ => 0, false⟩

theorem mach_ready {ns nr : ℕ} (cap : ℕ) {t s fuel : ℕ} {M : Machine t s} {input out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun M fuel input out) {tmap : Fin t → Fin (ns + 1)} (hinj : Function.Injective tmap)
    (σ : WState ns nr) (h0 : ∀ j, σ.sh (tmap j) = 0) (hin : ∀ j, σ.st (tmap j) = input j) :
    WXExec cap (.mach M tmap) σ (updS tmap σ (fun _ => 0) out) fuel := by
  obtain ⟨τ, e, hd⟩ := Dock.ready_mach cap h hinj σ h0 hin
  rwa [updS_eq tmap σ (fun _ => 0) out hinj τ hd.st hd.sh hd.other hd.val hd.cell]

section Run
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G) (A : OuterM.ARun mw SV) (h : H2D)

theorem mA_dIn : mA mw SV A h A.dIn = sS A.t h.t := by unfold mA; simp
theorem A_nd : A.dIn ≠ A.nIn ∧ A.dIn ≠ A.fOut ∧ A.dIn ≠ A.wOut ∧ A.nIn ≠ A.fOut ∧ A.nIn ≠ A.wOut ∧
    A.fOut ≠ A.wOut := by
  have nd := A.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  tauto
theorem h_nd : h.iW ≠ h.iD ∧ h.iW ≠ h.o ∧ h.iD ≠ h.o := by
  have nd := h.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at nd
  tauto
theorem mA_fOut : mA mw SV A h A.fOut = sFL A.t h.t := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A_nd mw SV A
  unfold mA; rw [if_neg (Ne.symm a2), if_neg (Ne.symm a4), if_pos rfl]
theorem mA_wOut : mA mw SV A h A.wOut = sW A.t h.t := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A_nd mw SV A
  unfold mA; rw [if_neg (Ne.symm a3), if_neg (Ne.symm a5), if_neg (Ne.symm a6), if_pos rfl]
theorem mH_iW : mH mw SV A h h.iW = sW A.t h.t := by unfold mH; simp
theorem mH_iD : mH mw SV A h h.iD = sPf A.t h.t := by
  obtain ⟨a1, a2, a3⟩ := h_nd h
  unfold mH; rw [if_neg (Ne.symm a1), if_pos rfl]
theorem mH_o : mH mw SV A h h.o = sOUT A.t h.t := by
  obtain ⟨a1, a2, a3⟩ := h_nd h
  unfold mH; rw [if_neg (Ne.symm a2), if_neg (Ne.symm a3), if_pos rfl]

/-- The A-run's map misses every stream outside `{1, 2, 3, 4}` and its private block. -/
theorem mA_ne (i : Fin (nsF A.t h.t + 1)) (h1 : i.val ≠ 1) (h2 : i.val ≠ 2) (h3 : i.val ≠ 3) (h4 : i.val ≠ 4)
    (hb : i.val < 13 ∨ 13 + A.t ≤ i.val) : ∀ j, mA mw SV A h j ≠ i := fun j e => by
  have hv := congrArg Fin.val e; rw [mA_val] at hv; have := j.isLt; split_ifs at hv <;> omega

theorem mH_ne (i : Fin (nsF A.t h.t + 1)) (h4 : i.val ≠ 4) (h5 : i.val ≠ 5) (h6 : i.val ≠ 6)
    (hb : i.val < 13 + A.t) : ∀ j, mH mw SV A h j ≠ i := fun j e => by
  have hv := congrArg Fin.val e; rw [mH_val] at hv; have := j.isLt; split_ifs at hv <;> omega

end Run

section Main
variable (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
  (SV : Outer.SuccinctVerifier H G) (A : OuterM.ARun mw SV) (h : H2D)

/-- The step count of the run (`ds, dp, dw, dc` = lengths of `⟨B_src⟩`, `⟨B_pf⟩`, the word of `C^O`, the descriptor of
`H_B`; `q` the width; `m = |H_B|`). -/
def costF (ν ds dp dw dc q m : ℕ) : ℕ :=
  20 * 2 ^ ν + 3 + powCostP (2 ^ ν) + (40 * ν + 10) + A.K * (ν + 1) ^ A.e + h.K * (dw + dp + q + 1) ^ h.e +
    2 * DescW.readCost dc + (34 * m + 7) + (34 * q + 7) + costKF G ν ds + 20

/-- The register capacity of the run. -/
def capF (G ν dc : ℕ) : ℕ := capKF G ν + 8 * 2 ^ ν + 8 * dc + 100

theorem front_run (ν : ℕ) (hν : 1 ≤ ν) (z : BitInput (2 ^ ν)) (B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν))) :
    ∃ τ, WXExec (capF G ν (PCPPNative.descriptor (Outer.Dat mw SV ν B).D).length) (frontP mw SV A h)
        (startF A.t h.t (List.ofFn z) (PCPPNative.descriptor B.src) (PCPPNative.descriptor B.pf)) τ
        (costF mw SV A h ν (PCPPNative.descriptor B.src).length (PCPPNative.descriptor B.pf).length
          (Outer.outC mw SV ν B.src).word.length (PCPPNative.descriptor (Outer.Dat mw SV ν B).D).length
          (Outer.width mw SV (2 ^ ν)) (Outer.Dat mw SV ν B).D.size) ∧
      τ.st (sFL A.t h.t) = [decide (Guard G ν z B)] ∧
      τ.st (sOUT A.t h.t) = RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) ∧
      τ.st (sSZ A.t h.t) = List.replicate (Outer.Dat mw SV ν B).D.size true ∧
      τ.st (sAR A.t h.t) = List.replicate (Outer.width mw SV (2 ^ ν)) true := by
  classical
  set V := (PCPPNative.descriptor (Outer.Dat mw SV ν B).D).length with hVdef
  set cap := capF G ν V with hcapdef
  set σ0 := startF A.t h.t (List.ofFn z) (PCPPNative.descriptor B.src) (PCPPNative.descriptor B.pf) with hσ0
  have hcap0 : capKF G ν + 8 * 2 ^ ν + 8 * V + 100 ≤ cap := le_rfl
  have hνN : ν < 2 ^ ν := Nat.lt_two_pow_self
  -- A. `rN := N`
  have hnum : WireExponent3_5.SelectionMachine.Sort.NumOn σ0 (sZ A.t h.t) (2 ^ ν)
      (RadixSemantics.value (List.ofFn z)) := by
    refine ⟨?_, rfl⟩
    have hb := WireExponent3_5.CompilerMachine.Emit.binary_value_self (List.ofFn z)
    rw [List.length_ofFn] at hb
    rw [hb]; rfl
  have eA := BinW.width_spec cap (A := sZ A.t h.t) (K := rN) (T := tW) (by decide) (2 ^ ν) _ σ0 hnum rfl rfl
    (by omega)
  set σA := σ0.setv rN (2 ^ ν) with hσA
  -- P. `rNu := ν`
  have eP := powP_exec (cap := cap) (sFT A.t h.t) (2 ^ ν) σA (by simp [hσA]) (Nat.one_le_two_pow)
    (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp (config := { decide := true }) [hσA, hσ0, startF, Function.update_apply])
    rfl rfl (by omega)
  rw [Nat.clog_pow 2 ν (by norm_num)] at eP
  set σP := (σA.setv rNu ν).sets (sFT A.t h.t) (powFlag (2 ^ ν)) with hσP
  -- U. `NU := 1^ν`
  have eU := NearCubicWires.WireExponent3_5.PrimAsm.HashCell.wrU_spec cap (sNU A.t h.t) pT1 rNu pT2 pT3
    (by decide) (by decide) (by decide) (by decide) (by decide) σP rfl rfl
    (by simp (config := { decide := true }) [hσP, hσA, hσ0, startF, Function.update_apply])
    (by simp (config := { decide := true }) [hσP, hσA, hσ0, startF, Function.update_apply])
    (by simp (config := { decide := true }) [hσP, hσA, hσ0, startF, Function.update_apply])
    (by simp [hσP]; omega)
  have hPnu : σP.val rNu = ν := by simp [hσP]
  rw [hPnu] at eU
  set σU := σP.sets (sNU A.t h.t) (List.replicate ν true) with hσU
  have Ust : ∀ i : Fin (nsF A.t h.t + 1), σU.st i = if i.val = 2 then List.replicate ν true
      else if i.val = 12 then powFlag (2 ^ ν) else σ0.st i := by
    intro i
    simp only [hσU, hσP, hσA, WState.sets_st, WState.setv_st, Function.update_apply, Fin.ext_iff, fx_val]
  have Ush : ∀ i, σU.sh i = 0 := fun i => rfl
  have Uval : σU.val = Function.update (Function.update (fun _ => 0) rN (2 ^ ν)) rNu ν := rfl
  -- R. the A-run
  obtain ⟨outA, hrA, hoD, hoN, hoF, hoW⟩ := A.run ν (Outer.width mw SV (2 ^ ν)) B.src
  have σ0st : ∀ i : Fin (nsF A.t h.t + 1), σ0.st i = if i.val = 0 then RepairOrdinary.frame (List.ofFn z)
      else if i.val = 3 then PCPPNative.descriptor B.src else if i.val = 5 then PCPPNative.descriptor B.pf
      else [] := fun i => rfl
  have eR := mach_ready cap hrA (mA_inj mw SV A h) σU (fun j => Ush _) (by
    intro j
    rw [Ust, σ0st]
    unfold OuterM.aBank
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := A_nd mw SV A
    have hv := mA_val mw SV A h j
    have hj := j.isLt
    by_cases h1 : j = A.dIn
    · subst h1; rw [if_pos rfl] at hv; rw [hv]; simp
    by_cases h2 : j = A.nIn
    · subst h2; rw [if_neg (Ne.symm a1), if_pos rfl] at hv; rw [hv]; simp [h1]
    rw [if_neg h1, if_neg h2] at hv
    rw [if_neg h1, if_neg h2]
    by_cases h3 : j = A.fOut
    · rw [if_pos h3] at hv; rw [hv]; simp
    by_cases h4 : j = A.wOut
    · rw [if_neg h3, if_pos h4] at hv; rw [hv]; simp
    rw [if_neg h3, if_neg h4] at hv
    rw [hv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)])
  set σR := updS (mA mw SV A h) σU (fun _ => 0) outA with hσR
  have Rst : ∀ i, (∀ j, mA mw SV A h j ≠ i) → σR.st i = σU.st i := fun i hi =>
    updS_st_other _ _ _ _ i hi
  have Rsh : ∀ i, σR.sh i = 0 := fun i => by
    rw [hσR, updS_sh_zero _ (mA_inj mw SV A h)]; split_ifs <;> rfl
  have RW : σR.st (sW A.t h.t) = (Outer.outC mw SV ν B.src).word := by
    rw [← mA_wOut mw SV A h, hσR, updS_st_slot _ _ _ _ (mA_inj mw SV A h), hoW]
  have RS : σR.st (sS A.t h.t) = PCPPNative.descriptor B.src := by
    rw [← mA_dIn mw SV A h, hσR, updS_st_slot _ _ _ _ (mA_inj mw SV A h), hoD]
  have RFL : σR.st (sFL A.t h.t) = [decide (Outer.SrcFits G ν B.src)] := by
    rw [← mA_fOut mw SV A h, hσR, updS_st_slot _ _ _ _ (mA_inj mw SV A h), hoF]
  have Rlow : ∀ i : Fin (nsF A.t h.t + 1), i.val ≠ 1 → i.val ≠ 2 → i.val ≠ 3 → i.val ≠ 4 →
      (i.val < 13 ∨ 13 + A.t ≤ i.val) → σR.st i = σU.st i := fun i h1 h2 h3 h4 hb =>
    Rst i (mA_ne mw SV A h i h1 h2 h3 h4 hb)

  obtain ⟨outH, hrH, hoO, -, -⟩ := h.run (Outer.outC mw SV ν B.src) B.pf
  obtain ⟨b1, b2, b3⟩ := h_nd h
  have eH := mach_ready cap hrH (mH_inj mw SV A h) σR (fun j => Rsh _) (by
    intro j
    unfold CheckedPCPP.portBank
    by_cases h1 : j = h.iW
    · subst h1; rw [mH_iW, if_pos rfl, RW]
    by_cases h2 : j = h.iD
    · subst h2; rw [mH_iD, if_neg h1, if_pos rfl, Rlow _ (by simp) (by simp) (by simp) (by simp) (by simp), Ust,
        σ0st]; simp
    rw [if_neg h1, if_neg h2]
    have hv := mH_val mw SV A h j
    rw [if_neg h1, if_neg h2] at hv
    have hj := j.isLt
    by_cases h3 : j = h.o
    · rw [if_pos h3] at hv
      rw [Rlow _ (by omega) (by omega) (by omega) (by omega) (by omega), Ust, σ0st, hv]; simp
    rw [if_neg h3] at hv
    rw [Rlow _ (by omega) (by omega) (by omega) (by omega) (by omega), Ust, σ0st, hv, if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)])
  set σH := updS (mH mw SV A h) σR (fun _ => 0) outH with hσH
  have Hst : ∀ i, (∀ j, mH mw SV A h j ≠ i) → σH.st i = σR.st i := fun i hi =>
    updS_st_other _ _ _ _ i hi
  have Hsh : ∀ i, σH.sh i = 0 := fun i => by
    rw [hσH, updS_sh_zero _ (mH_inj mw SV A h)]; split_ifs
    · rfl
    · exact Rsh i
  have HOUT : σH.st (sOUT A.t h.t) = RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) := by
    rw [← mH_o mw SV A h, hσH, updS_st_slot _ _ _ _ (mH_inj mw SV A h), hoO]; rfl
  have Hlow : ∀ i : Fin (nsF A.t h.t + 1), i.val ≠ 4 → i.val ≠ 5 → i.val ≠ 6 → i.val < 13 + A.t →
      σH.st i = σR.st i := fun i h4 h5 h6 hb => Hst i (mH_ne mw SV A h i h4 h5 h6 hb)
  have Hval : σH.val = Function.update (Function.update (fun _ => 0) rN (2 ^ ν)) rNu ν := rfl
  have Hsmall : ∀ r : Fin nrW, r.val < 19 → σH.val r = 0 := fun r hr => by
    rw [Hval, Function.update_apply, if_neg (fun e => by rw [e] at hr; exact absurd hr (by decide)),
      Function.update_apply, if_neg (fun e => by rw [e] at hr; exact absurd hr (by decide))]
  -- S. `q = n` and `|H_B| = m` (the first two fields of `descriptor H_B`), then `1^m` on `SZ`, `1^q` on `AR`
  have hdesc := PCPPNative.descriptor_eq (Outer.Dat mw SV ν B).D
  have hframe : RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) =
      [] ++ marks (natWord (Outer.Dat mw SV ν B).n) ++ (marks (natWord (Outer.Dat mw SV ν B).D.nodes.length) ++
        (marks ((Outer.Dat mw SV ν B).D.nodes.flatMap PCPPRequestNodeSchema.native ++
          natWord (Outer.Dat mw SV ν B).D.output.val) ++ [false])) := by
    rw [DescW.frame_eq_marks', hdesc]
    simp only [Streaming.marks_append, List.append_assoc, List.nil_append]
  have hmV : (Outer.Dat mw SV ν B).D.nodes.length ≤ V := by
    have := DescW.length_le_bytes (Outer.Dat mw SV ν B).D.nodes
    rw [hVdef, hdesc]; simp only [List.length_append]; omega
  have hnV : (Outer.Dat mw SV ν B).n ≤ V := (Outer.Dat mw SV ν B).sizeAtLeast.trans hmV
  have eG1 := DescW.readG_spec cap Hr (sOUT A.t h.t) 9 (by decide) _ V hnV [] _ σH (by rw [HOUT, hframe])
    (by rw [Hsh]; rfl) (fun i _ => Hsmall _ (by rw [ChecksW.Rw_apply, DescW.GH]; simp; omega))
    (by rw [DescW.g9, Hsmall _ (by simp)]; omega)
  rw [DescW.g9, Hsmall _ (by simp), Nat.zero_add] at eG1
  set σ1 := (σH.seth (sOUT A.t h.t) ([].length + 2 * (natWord (Outer.Dat mw SV ν B).n).length)).setv (Hr 9)
    (Outer.Dat mw SV ν B).n with hσ1
  have eG2 := DescW.readG_spec cap Hr (sOUT A.t h.t) 10 (by decide) _ V hmV
    (marks (natWord (Outer.Dat mw SV ν B).n)) (marks ((Outer.Dat mw SV ν B).D.nodes.flatMap
      PCPPRequestNodeSchema.native ++ natWord (Outer.Dat mw SV ν B).D.output.val) ++ [false]) σ1
    (by rw [hσ1]; simp only [WState.setv_st, WState.seth_st]; rw [HOUT, hframe]
        simp only [List.nil_append, List.append_assoc])
    (by simp [hσ1]) (fun i _ => by
      rw [ChecksW.Rw_apply, DescW.GH, hσ1, WState.setv_val, Function.update_apply, if_neg (fun e => by
        have := congrArg Fin.val e; simp at this; omega)]
      exact Hsmall _ (by simp; omega))
    (by rw [DescW.g10, hσ1, WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val,
      Hsmall _ (by simp)]; omega)
  rw [DescW.g10] at eG2
  have v10 : σ1.val (Hr 10) = 0 := by
    rw [hσ1, WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val, Hsmall _ (by simp)]
  rw [v10, Nat.zero_add] at eG2
  set σ2 := (σ1.seth (sOUT A.t h.t) ((marks (natWord (Outer.Dat mw SV ν B).n)).length +
    2 * (natWord (Outer.Dat mw SV ν B).D.nodes.length).length)).setv (Hr 10)
    (Outer.Dat mw SV ν B).D.nodes.length with hσ2
  have v2 : ∀ r : Fin nrW, r ≠ Hr 9 → r ≠ Hr 10 → σ2.val r = σH.val r := fun r h9 h10 => by
    rw [hσ2, WState.setv_val, Function.update_apply, if_neg h10, WState.seth_val, hσ1, WState.setv_val,
      Function.update_apply, if_neg h9, WState.seth_val]
  have st2 : σ2.st = σH.st := by rw [hσ2, hσ1]; rfl
  have sh2 : ∀ i, i ≠ sOUT A.t h.t → σ2.sh i = 0 := fun i hi => by
    rw [hσ2, WState.setv_sh, WState.seth_sh, Function.update_of_ne hi, hσ1, WState.setv_sh, WState.seth_sh,
      Function.update_of_ne hi, Hsh]
  have eW1 := TabMachine.writeOnes_spec cap (X := sSZ A.t h.t) (K := Hr 10) (K2 := Hr 11) (by decide) σ2
    (Outer.Dat mw SV ν B).D.nodes.length
    (by rw [st2, Hlow _ (by simp) (by simp) (by simp) (by simp; omega), Rlow _ (by simp) (by simp) (by simp) (by simp)
      (by simp), Ust, σ0st]; simp)
    (sh2 _ (by simp [Fin.ext_iff])) (by rw [hσ2]; simp)
    (by rw [v2 _ (by decide) (by decide)]; exact Hsmall _ (by simp)) (by omega)
  set σ3 := σ2.sets (sSZ A.t h.t) (List.replicate (Outer.Dat mw SV ν B).D.nodes.length true) with hσ3
  have eW2 := TabMachine.writeOnes_spec cap (X := sAR A.t h.t) (K := Hr 9) (K2 := Hr 11) (by decide) σ3
    (Outer.Dat mw SV ν B).n
    (by rw [hσ3, WState.sets_st, Function.update_of_ne (by simp [Fin.ext_iff]), st2,
      Hlow _ (by simp) (by simp) (by simp) (by simp; omega), Rlow _ (by simp) (by simp) (by simp) (by simp) (by simp), Ust,
      σ0st]; simp)
    (by rw [hσ3, WState.sets_sh]; exact sh2 _ (by simp [Fin.ext_iff]))
    (by rw [hσ3, WState.sets_val, hσ2, WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val]
        simp [hσ1])
    (by rw [hσ3, WState.sets_val, v2 _ (by decide) (by decide)]; exact Hsmall _ (by simp)) (by omega)
  set σ4 := σ3.sets (sAR A.t h.t) (List.replicate (Outer.Dat mw SV ν B).n true) with hσ4
  -- the state before phase K
  have st4 : ∀ i : Fin (nsF A.t h.t + 1), i.val ≠ 7 → i.val ≠ 8 → σ4.st i = σH.st i := fun i h7 h8 => by
    rw [hσ4, WState.sets_st, Function.update_of_ne (fun e => h8 (by rw [e]; rfl)), hσ3, WState.sets_st,
      Function.update_of_ne (fun e => h7 (by rw [e]; rfl)), st2]
  have sh4 : ∀ i, i ≠ sOUT A.t h.t → σ4.sh i = 0 := fun i hi => by rw [hσ4, hσ3]; exact sh2 i hi
  have v4 : ∀ r : Fin nrW, r ≠ Hr 9 → r ≠ Hr 10 → σ4.val r = σH.val r := fun r h9 h10 => by
    rw [hσ4, WState.sets_val, hσ3, WState.sets_val]; exact v2 r h9 h10
  have low4 : ∀ i : Fin (nsF A.t h.t + 1), 7 ≤ i.val → i.val < 13 → σ4.st i = σ0.st i ∨ i.val = 7 ∨ i.val = 8 ∨
      i.val = 12 := fun i h1 h2 => by
    by_cases h7 : i.val = 7
    · exact Or.inr (Or.inl h7)
    by_cases h8 : i.val = 8
    · exact Or.inr (Or.inr (Or.inl h8))
    by_cases h12 : i.val = 12
    · exact Or.inr (Or.inr (Or.inr h12))
    left
    rw [st4 i h7 h8, Hlow _ (by omega) (by omega) (by omega) (by omega), Rlow _ (by omega) (by omega) (by omega)
      (by omega) (by omega), Ust, if_neg (by omega), if_neg h12]
  have blank4 : ∀ i : Fin (nsF A.t h.t + 1), 9 ≤ i.val → i.val < 12 → σ4.st i = [] := fun i h1 h2 => by
    rcases low4 i (by omega) (by omega) with e | e | e | e
    · rw [e, σ0st, if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    all_goals omega
  have FL4 : σ4.st (sFL A.t h.t) = [decide (Outer.SrcFits G ν B.src)] := by
    rw [st4 _ (by simp) (by simp), Hlow _ (by simp) (by simp) (by simp) (by simp; omega), RFL]
  have OUT4 : σ4.st (sOUT A.t h.t) = RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) := by
    rw [st4 _ (by simp) (by simp), HOUT]
  have SZ4 : σ4.st (sSZ A.t h.t) = List.replicate (Outer.Dat mw SV ν B).D.size true := by
    rw [hσ4, WState.sets_st, Function.update_of_ne (by simp [Fin.ext_iff]), hσ3, WState.sets_st,
      Function.update_self]; rfl
  have AR4 : σ4.st (sAR A.t h.t) = List.replicate (Outer.width mw SV (2 ^ ν)) true := by
    rw [hσ4, WState.sets_st, Function.update_self]; rfl
  have hw4 : wbit σ4 (sFL A.t h.t) = decide (Outer.SrcFits G ν B.src) := by
    unfold wbit; rw [FL4, sh4 _ (by simp [Fin.ext_iff])]; rfl
  have hcost : ∀ nK, nK ≤ costKF G ν (PCPPNative.descriptor B.src).length + 1 →
      20 * 2 ^ ν + 3 + 1 + (powCostP (2 ^ ν) + 1 + (40 * ν + 10 + 1 + (A.K * (ν + 1) ^ A.e + 1 +
        (h.K * ((Outer.outC mw SV ν B.src).word.length + (PCPPNative.descriptor B.pf).length +
          Outer.width mw SV (2 ^ ν) + 1) ^ h.e + 1 + (DescW.readCost V + 1 + (DescW.readCost V + 1 +
        (34 * (Outer.Dat mw SV ν B).D.nodes.length + 7 + 1 + (34 * (Outer.Dat mw SV ν B).n + 7 + 1 + nK)))))))) ≤
      costF mw SV A h ν (PCPPNative.descriptor B.src).length (PCPPNative.descriptor B.pf).length
          (Outer.outC mw SV ν B.src).word.length V (Outer.width mw SV (2 ^ ν)) (Outer.Dat mw SV ν B).D.size := by
    intro nK hK
    unfold costF
    have e1 : (Outer.Dat mw SV ν B).D.size = (Outer.Dat mw SV ν B).D.nodes.length := rfl
    have e2 : (Outer.Dat mw SV ν B).n = Outer.width mw SV (2 ^ ν) := rfl
    omega
  by_cases hf : Outer.SrcFits G ν B.src
  · obtain ⟨τ, eK, hFLτ, hoth⟩ := phKF_exec A.t h.t G ν z B.src cap hν hf (by omega) σ4
      (by rw [st4 _ (by simp) (by simp), Hlow _ (by simp) (by simp) (by simp) (by simp; omega), RS])
      (sh4 _ (by simp [Fin.ext_iff]))
      (by rw [st4 _ (by simp) (by simp), Hlow _ (by simp) (by simp) (by simp) (by simp),
        Rlow _ (by simp) (by simp) (by simp) (by simp) (by simp), Ust, σ0st]; simp)
      (sh4 _ (by simp [Fin.ext_iff]))
      (blank4 _ (by simp) (by simp)) (sh4 _ (by simp [Fin.ext_iff]))
      (blank4 _ (by simp) (by simp)) (sh4 _ (by simp [Fin.ext_iff]))
      (blank4 _ (by simp) (by simp)) (sh4 _ (by simp [Fin.ext_iff]))
      (by rw [FL4, decide_eq_true hf]) (sh4 _ (by simp [Fin.ext_iff]))
      (by rw [v4 _ (by decide) (by decide), Hval]; simp (config := { decide := true }) [Function.update_apply])
      (by rw [v4 _ (by decide) (by decide), Hval]; simp (config := { decide := true }) [Function.update_apply])
      (fun r hr h1 h2 => by
        rw [v4 _ (fun e => by rw [e] at hr; exact absurd hr (by decide))
          (fun e => by rw [e] at hr; exact absurd hr (by decide)), Hval, Function.update_apply, if_neg h2,
          Function.update_apply, if_neg h1])
    refine ⟨τ, WXExec.mono (WXExec.seq eA (WXExec.seq eP (WXExec.seq (WXExec.wm eU) (WXExec.seq eR
      (WXExec.seq eH (WXExec.seq (WXExec.wm eG1) (WXExec.seq (WXExec.wm eG2) (WXExec.seq eW1 (WXExec.seq eW2
      (WXExec.ifsT (by rw [hw4]; simp [hf]) eK)))))))))) (hcost _ le_rfl), ?_, ?_, ?_, ?_⟩
    · rw [hFLτ]
      congr 1
      exact decide_eq_decide.mpr ⟨fun hc => ⟨hf, hc⟩, fun hg => hg.2⟩
    · rw [hoth _ (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
      exact OUT4
    · rw [hoth _ (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
      exact SZ4
    · rw [hoth _ (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff])]
      exact AR4
  · refine ⟨σ4, WXExec.mono (WXExec.seq eA (WXExec.seq eP (WXExec.seq (WXExec.wm eU) (WXExec.seq eR
      (WXExec.seq eH (WXExec.seq (WXExec.wm eG1) (WXExec.seq (WXExec.wm eG2) (WXExec.seq eW1 (WXExec.seq eW2
      (WXExec.ifsF (by rw [hw4]; simp [hf]) (WXExec.skip cap σ4))))))))))) (hcost _ (by omega)), ?_, OUT4, SZ4,
      AR4⟩
    rw [FL4]
    congr 1
    rw [decide_eq_false hf, decide_eq_false (fun hg : Guard G ν z B => hf hg.1)]

end Main

end W3.NearCubicWires.RepairSource.Outer3.Front
