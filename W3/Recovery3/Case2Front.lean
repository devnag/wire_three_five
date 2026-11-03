import W3.Recovery3.Case2Exec
import W3.Front.Main
import W3.Recovery3.After4Mach

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (updS)
open NearCubicWires.RepairOrdinary.Streaming (marks)
open NearCubicWires.RepairRepresentation (natWord)

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

open Front

noncomputable abbrev UF := NearCubicGates.Close.Recovery3.After.unframe

def ns2 (tu th : ℕ) : ℕ := 7 + tu + th

section Layout
variable (tu th : ℕ)

def gx (k : ℕ) (hk : k < 8) : Fin (ns2 tu th + 1) := ⟨k, by unfold ns2; omega⟩
abbrev tW0 := gx tu th 0 (by decide)
abbrev tFD := gx tu th 1 (by decide)
abbrev tFA := gx tu th 2 (by decide)
abbrev tFD2 := gx tu th 3 (by decide)
abbrev tPf := gx tu th 4 (by decide)
abbrev tOUT := gx tu th 5 (by decide)
abbrev tSZ := gx tu th 6 (by decide)
abbrev tAR := gx tu th 7 (by decide)
@[simp] theorem gx_val (k : ℕ) (hk : k < 8) : (gx tu th k hk).val = k := rfl

end Layout

noncomputable def mU (h : H2D) (j : Fin UF.t) : Fin (ns2 UF.t h.t + 1) :=
  if j = UF.src then tFD2 UF.t h.t else if j = UF.dst then tPf UF.t h.t
  else ⟨8 + j.val, by unfold ns2; have := j.isLt; omega⟩

noncomputable def mH2 (h : H2D) (j : Fin h.t) : Fin (ns2 UF.t h.t + 1) :=
  if j = h.iW then tW0 UF.t h.t else if j = h.iD then tPf UF.t h.t else if j = h.o then tOUT UF.t h.t
  else ⟨8 + UF.t + j.val, by unfold ns2; have := j.isLt; omega⟩

theorem mU_val (h : H2D) (j : Fin UF.t) : (mU h j).val =
    if j = UF.src then 3 else if j = UF.dst then 4 else 8 + j.val := by
  unfold mU; split_ifs <;> rfl

theorem mH2_val (h : H2D) (j : Fin h.t) : (mH2 h j).val =
    if j = h.iW then 0 else if j = h.iD then 4 else if j = h.o then 5 else 8 + UF.t + j.val := by
  unfold mH2; split_ifs <;> rfl

theorem mU_inj (h : H2D) : Function.Injective (mU h) := by
  have hne := UF.ne
  intro i j hij
  have hv := congrArg Fin.val hij
  rw [mU_val, mU_val] at hv
  split_ifs at hv <;> first | (subst_vars; rfl) | (exfalso; omega) | (exact Fin.ext (by omega))

theorem mH2_inj (h : H2D) : Function.Injective (mH2 h) := by
  intro i j hij
  have hv := congrArg Fin.val hij
  rw [mH2_val, mH2_val] at hv
  split_ifs at hv <;> first | (subst_vars; rfl) | (exfalso; omega) | (exact Fin.ext (by omega))

theorem mU_ne (h : H2D) (i : Fin (ns2 UF.t h.t + 1)) (h3 : i.val ≠ 3) (h4 : i.val ≠ 4)
    (hb : i.val < 8 ∨ 8 + UF.t ≤ i.val) : ∀ j, mU h j ≠ i := fun j e => by
  have hv := congrArg Fin.val e; rw [mU_val] at hv; have := j.isLt; split_ifs at hv <;> omega

theorem mH2_ne (h : H2D) (i : Fin (ns2 UF.t h.t + 1)) (h0 : i.val ≠ 0) (h4 : i.val ≠ 4) (h5 : i.val ≠ 5)
    (hb : i.val < 8 + UF.t) : ∀ j, mH2 h j ≠ i := fun j e => by
  have hv := congrArg Fin.val e; rw [mH2_val] at hv; have := j.isLt; split_ifs at hv <;> omega

theorem mU_dst (h : H2D) : mU h UF.dst = tPf UF.t h.t := by
  unfold mU; rw [if_neg (Ne.symm UF.ne), if_pos rfl]
theorem mH2_iW (h : H2D) : mH2 h h.iW = tW0 UF.t h.t := by unfold mH2; simp
theorem mH2_iD (h : H2D) : mH2 h h.iD = tPf UF.t h.t := by
  obtain ⟨a1, a2, a3⟩ := h_nd h
  unfold mH2; rw [if_neg (Ne.symm a1), if_pos rfl]
theorem mH2_o (h : H2D) : mH2 h h.o = tOUT UF.t h.t := by
  obtain ⟨a1, a2, a3⟩ := h_nd h
  unfold mH2; rw [if_neg (Ne.symm a2), if_neg (Ne.symm a3), if_pos rfl]

/-- Scratch registers of the copy. -/
def rOP : Fin nrW := ⟨20, by decide⟩
def rT : Fin nrW := ⟨21, by decide⟩
def rD : Fin nrW := ⟨22, by decide⟩

/-- **The Case-2 front's program.** -/
noncomputable def front2P (h : H2D) : WMX (ns2 UF.t h.t) nrW :=
  .seq (.wm (Codec.copyRW (tFD UF.t h.t) (tFD2 UF.t h.t) rOP rT rD))
  (.seq (.mach UF.M (mU h))
  (.seq (.mach h.M (mH2 h))
  (.seq (.wm (CheckedPCPP.DescW.readG Hr (tOUT UF.t h.t) 9))
  (.seq (.wm (CheckedPCPP.DescW.readG Hr (tOUT UF.t h.t) 10))
  (.seq (TabMachine.writeOnes (tSZ UF.t h.t) (Hr 10) (Hr 11))
  (TabMachine.writeOnes (tAR UF.t h.t) (Hr 9) (Hr 11)))))))

def start2 (tu th : ℕ) (w d address : List Bool) : WState (ns2 tu th) nrW :=
  ⟨fun _ => 0, fun i => if i.val = 0 then w else if i.val = 1 then RepairOrdinary.frame d
    else if i.val = 2 then RepairOrdinary.frame address else [], fun _ => 0, false⟩

noncomputable def cost2 (h : H2D) (dw dd dc q m : ℕ) : ℕ :=
  (22 * dd + 1 + 1 + 7 + 1 + (18 * (2 * dd + 1) + 3 + 1 + (5 * (2 * dd + 1) + 1 + 1 + (5 * (2 * dd + 1) + 1)))) +
    UF.K * (dd + 1) + h.K * (dw + dd + q + 1) ^ h.e + 2 * DescW.readCost dc + (34 * m + 7) + (34 * q + 7) + 20

def cap2 (dd dc : ℕ) : ℕ := 4 * dd + 8 * dc + 100

theorem front2_run (h : H2D) (oc : NearCubicWires.Bindings.MW20.OracleOutput) {q : ℕ} (B : BooleanCircuit q)
    (address : List Bool) :
    ∃ τ, WXExec (cap2 (PCPPNative.descriptor B).length
        (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity).length) (front2P h)
        (start2 UF.t h.t oc.word (PCPPNative.descriptor B) address) τ
        (cost2 h oc.word.length (PCPPNative.descriptor B).length
          (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity).length q
          (Outer.substCircuit oc.circuit B).padToArity.size) ∧
      τ.st (tW0 UF.t h.t) = oc.word ∧ τ.st (tFD UF.t h.t) = RepairOrdinary.frame (PCPPNative.descriptor B) ∧
      τ.st (tFA UF.t h.t) = RepairOrdinary.frame address ∧
      τ.st (tOUT UF.t h.t) = RepairOrdinary.frame (PCPPNative.descriptor (Outer.substCircuit oc.circuit B).padToArity) ∧
      τ.st (tSZ UF.t h.t) = List.replicate (Outer.substCircuit oc.circuit B).padToArity.size true ∧
      τ.st (tAR UF.t h.t) = List.replicate q true := by
  classical
  set Hc := (Outer.substCircuit oc.circuit B).padToArity with hHc
  set dd := (PCPPNative.descriptor B).length with hdd
  set V := (PCPPNative.descriptor Hc).length with hVdef
  set cap := cap2 dd V with hcapdef
  set σ0 := start2 UF.t h.t oc.word (PCPPNative.descriptor B) address with hσ0
  have σ0st : ∀ i : Fin (ns2 UF.t h.t + 1), σ0.st i = if i.val = 0 then oc.word
      else if i.val = 1 then RepairOrdinary.frame (PCPPNative.descriptor B)
      else if i.val = 2 then RepairOrdinary.frame address else [] := fun i => rfl

  have e1 := Codec.copyRW_spec cap (tFD UF.t h.t) (tFD2 UF.t h.t) (by simp [Fin.ext_iff]) rOP rT rD (by decide)
    (by decide) (by decide) (PCPPNative.descriptor B) [] σ0 (by rw [σ0st]; simp) rfl rfl rfl rfl rfl rfl
    (by rw [hcapdef]; unfold cap2; omega)
  set σ1 := σ0.sets (tFD2 UF.t h.t) (RepairOrdinary.frame (PCPPNative.descriptor B)) with hσ1
  have σ1st : ∀ i : Fin (ns2 UF.t h.t + 1), σ1.st i = if i.val = 3 then RepairOrdinary.frame (PCPPNative.descriptor B)
      else σ0.st i := by
    intro i; simp only [hσ1, WState.sets_st, Function.update_apply, Fin.ext_iff, gx_val]
  -- 2. the unframe
  obtain ⟨outU, hrU, hoU⟩ := UF.run (PCPPNative.descriptor B)
  have eU := mach_ready cap hrU (mU_inj h) σ1 (fun j => rfl) (by
    intro j
    unfold NearCubicGates.Close.Recovery3.After.oneBank
    have hv := mU_val h j
    rw [σ1st, σ0st]
    by_cases h1 : j = UF.src
    · subst h1; rw [if_pos rfl] at hv; rw [hv, if_pos rfl]; simp
    rw [if_neg h1] at hv ⊢
    by_cases h2 : j = UF.dst
    · rw [if_pos h2] at hv; rw [hv]; simp
    rw [if_neg h2] at hv
    rw [hv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)])
  set σU := updS (mU h) σ1 (fun _ => 0) outU with hσU
  have Ush : ∀ i, σU.sh i = 0 := fun i => by
    rw [hσU, updS_sh_zero _ (mU_inj h)]; split_ifs <;> rfl
  have UPf : σU.st (tPf UF.t h.t) = PCPPNative.descriptor B := by
    rw [← mU_dst h, hσU, updS_st_slot _ _ _ _ (mU_inj h), hoU]
  have Ulow : ∀ i : Fin (ns2 UF.t h.t + 1), i.val ≠ 3 → i.val ≠ 4 → (i.val < 8 ∨ 8 + UF.t ≤ i.val) →
      σU.st i = σ1.st i := fun i h3 h4 hb => updS_st_other _ _ _ _ i (mU_ne h i h3 h4 hb)

  obtain ⟨outH, hrH, hoO, hoW, hoD⟩ := h.run oc B
  have eH := mach_ready cap hrH (mH2_inj h) σU (fun j => Ush _) (by
    intro j
    unfold CheckedPCPP.portBank
    by_cases h1 : j = h.iW
    · subst h1; rw [mH2_iW, if_pos rfl, Ulow _ (by simp) (by simp) (by simp), σ1st, σ0st]; simp
    by_cases h2 : j = h.iD
    · subst h2; rw [mH2_iD, if_neg h1, if_pos rfl, UPf]
    rw [if_neg h1, if_neg h2]
    have hv := mH2_val h j
    rw [if_neg h1, if_neg h2] at hv
    have hj := j.isLt
    by_cases h3 : j = h.o
    · rw [if_pos h3] at hv
      rw [Ulow _ (by omega) (by omega) (by omega), σ1st, σ0st, hv]; simp
    rw [if_neg h3] at hv
    rw [Ulow _ (by omega) (by omega) (by omega), σ1st, σ0st, hv, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)])
  set σH := updS (mH2 h) σU (fun _ => 0) outH with hσH
  have Hsh : ∀ i, σH.sh i = 0 := fun i => by
    rw [hσH, updS_sh_zero _ (mH2_inj h)]; split_ifs
    · rfl
    · exact Ush i
  have HOUT : σH.st (tOUT UF.t h.t) = RepairOrdinary.frame (PCPPNative.descriptor Hc) := by
    rw [← mH2_o h, hσH, updS_st_slot _ _ _ _ (mH2_inj h), hoO]
  have HW0 : σH.st (tW0 UF.t h.t) = oc.word := by
    rw [← mH2_iW h, hσH, updS_st_slot _ _ _ _ (mH2_inj h), hoW]
  have Hlow : ∀ i : Fin (ns2 UF.t h.t + 1), i.val ≠ 0 → i.val ≠ 4 → i.val ≠ 5 → i.val < 8 + UF.t →
      σH.st i = σU.st i := fun i h0 h4 h5 hb => updS_st_other _ _ _ _ i (mH2_ne h i h0 h4 h5 hb)
  have Hval : σH.val = fun _ => 0 := rfl
  -- 4. `q` and `|H_B|`
  have hdesc := PCPPNative.descriptor_eq Hc
  have hframe : RepairOrdinary.frame (PCPPNative.descriptor Hc) =
      [] ++ marks (natWord q) ++ (marks (natWord Hc.nodes.length) ++
        (marks (Hc.nodes.flatMap PCPPRequestNodeSchema.native ++ natWord Hc.output.val) ++ [false])) := by
    rw [DescW.frame_eq_marks', hdesc]
    simp only [Streaming.marks_append, List.append_assoc, List.nil_append]
  have hmV : Hc.nodes.length ≤ V := by
    have := DescW.length_le_bytes Hc.nodes
    rw [hVdef, hdesc]; simp only [List.length_append]; omega
  have hnV : q ≤ V := (BooleanCircuit.arity_le_padToArity_size _).trans hmV
  have eG1 := DescW.readG_spec cap Hr (tOUT UF.t h.t) 9 (by decide) _ V hnV [] _ σH (by rw [HOUT, hframe])
    (by rw [Hsh]; rfl) (fun i _ => by rw [Hval]) (by rw [DescW.g9, Hval]; simp [hcapdef, cap2]; omega)
  rw [DescW.g9, Hval, Nat.zero_add] at eG1
  set σ1' := (σH.seth (tOUT UF.t h.t) ([].length + 2 * (natWord q).length)).setv (Hr 9) q with hσ1'
  have eG2 := DescW.readG_spec cap Hr (tOUT UF.t h.t) 10 (by decide) _ V hmV (marks (natWord q))
    (marks (Hc.nodes.flatMap PCPPRequestNodeSchema.native ++ natWord Hc.output.val) ++ [false]) σ1'
    (by rw [hσ1']; simp only [WState.setv_st, WState.seth_st]; rw [HOUT, hframe]
        simp only [List.nil_append, List.append_assoc])
    (by simp [hσ1']) (fun i _ => by
      rw [ChecksW.Rw_apply, DescW.GH, hσ1', WState.setv_val, Function.update_apply, if_neg (fun e => by
        have := congrArg Fin.val e; simp at this; omega)]
      rfl)
    (by rw [DescW.g10, hσ1', WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val, Hval]
        simp [hcapdef, cap2]; omega)
  rw [DescW.g10] at eG2
  have v10 : σ1'.val (Hr 10) = 0 := by
    rw [hσ1', WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val, Hval]
  rw [v10, Nat.zero_add] at eG2
  set σ2 := (σ1'.seth (tOUT UF.t h.t) ((marks (natWord q)).length + 2 * (natWord Hc.nodes.length).length)).setv
    (Hr 10) Hc.nodes.length with hσ2
  have st2 : σ2.st = σH.st := by rw [hσ2, hσ1']; rfl
  have sh2 : ∀ i, i ≠ tOUT UF.t h.t → σ2.sh i = 0 := fun i hi => by
    rw [hσ2, WState.setv_sh, WState.seth_sh, Function.update_of_ne hi, hσ1', WState.setv_sh, WState.seth_sh,
      Function.update_of_ne hi, Hsh]
  have blankSZ : σH.st (tSZ UF.t h.t) = [] := by
    rw [Hlow _ (by simp) (by simp) (by simp) (by simp; omega), Ulow _ (by simp) (by simp) (by simp), σ1st, σ0st]
    simp
  have blankAR : σH.st (tAR UF.t h.t) = [] := by
    rw [Hlow _ (by simp) (by simp) (by simp) (by simp; omega), Ulow _ (by simp) (by simp) (by simp), σ1st, σ0st]
    simp
  have eW1 := TabMachine.writeOnes_spec cap (X := tSZ UF.t h.t) (K := Hr 10) (K2 := Hr 11) (by decide) σ2
    Hc.nodes.length (by rw [st2]; exact blankSZ) (sh2 _ (by simp [Fin.ext_iff])) (by rw [hσ2]; simp)
    (by rw [hσ2, WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val, hσ1',
        WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val, Hval])
    (by simp [hcapdef, cap2]; omega)
  set σ3 := σ2.sets (tSZ UF.t h.t) (List.replicate Hc.nodes.length true) with hσ3
  have eW2 := TabMachine.writeOnes_spec cap (X := tAR UF.t h.t) (K := Hr 9) (K2 := Hr 11) (by decide) σ3 q
    (by rw [hσ3, WState.sets_st, Function.update_of_ne (by simp [Fin.ext_iff]), st2]; exact blankAR)
    (by rw [hσ3, WState.sets_sh]; exact sh2 _ (by simp [Fin.ext_iff]))
    (by rw [hσ3, WState.sets_val, hσ2, WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val]
        simp [hσ1'])
    (by rw [hσ3, WState.sets_val, hσ2, WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val,
        hσ1', WState.setv_val, Function.update_apply, if_neg (by decide), WState.seth_val, Hval])
    (by simp [hcapdef, cap2]; omega)
  set σ4 := σ3.sets (tAR UF.t h.t) (List.replicate q true) with hσ4
  have st4 : ∀ i : Fin (ns2 UF.t h.t + 1), i.val ≠ 6 → i.val ≠ 7 → σ4.st i = σH.st i := fun i h6 h7 => by
    rw [hσ4, WState.sets_st, Function.update_of_ne (fun e => h7 (by rw [e]; rfl)), hσ3, WState.sets_st,
      Function.update_of_ne (fun e => h6 (by rw [e]; rfl)), st2]
  refine ⟨σ4, WXExec.mono (WXExec.seq (WXExec.wm e1) (WXExec.seq eU (WXExec.seq eH (WXExec.seq (WXExec.wm eG1)
    (WXExec.seq (WXExec.wm eG2) (WXExec.seq eW1 eW2)))))) ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold cost2
    have e : Hc.size = Hc.nodes.length := rfl
    rw [e, hdd]
    omega
  · rw [st4 _ (by simp) (by simp)]; exact HW0
  · rw [st4 _ (by simp) (by simp), Hlow _ (by simp) (by simp) (by simp) (by simp; omega),
      Ulow _ (by simp) (by simp) (by simp), σ1st, σ0st]; simp
  · rw [st4 _ (by simp) (by simp), Hlow _ (by simp) (by simp) (by simp) (by simp; omega),
      Ulow _ (by simp) (by simp) (by simp), σ1st, σ0st]; simp
  · rw [st4 _ (by simp) (by simp)]; exact HOUT
  · rw [hσ4, WState.sets_st, Function.update_of_ne (by simp [Fin.ext_iff]), hσ3, WState.sets_st,
      Function.update_self]; rfl
  · rw [hσ4, WState.sets_st, Function.update_self]

end W3.NearCubicWires.RepairSource.Outer3.Case2
