import W3.Front.Cost

set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP

namespace W3.NearCubicWires.RepairSource.Outer3.Front

theorem frontBank_apply (T : ℕ) (zIn sIn pIn : Fin T) (z s p : List Bool) (i : Fin T) :
    frontBank T zIn sIn pIn z s p i = if i.val = zIn.val then RepairOrdinary.frame z else if i.val = sIn.val then s
      else if i.val = pIn.val then p else [] := by
  unfold frontBank; simp only [Fin.ext_iff]

open NearCubicWires.WireExponent3_5.PrimAsm.DockW in
/-- The cold bank of the start is JF's entry bank. -/
theorem bank_eqF (ta th : ℕ) (z s p : List Bool) :
    Fin.addCases (motive := fun _ => List Bool) (CheckedPCPP.coldBank (startF ta th z s p)) (fun _ : Fin 1 => []) =
      frontBank (nsF ta th + 2 + nrW + 1) (Fin.castAdd 1 (sTape (nr := nrW) (sZ ta th)))
        (Fin.castAdd 1 (sTape (nr := nrW) (sS ta th))) (Fin.castAdd 1 (sTape (nr := nrW) (sPf ta th))) z s p := by
  have hz : (Fin.castAdd 1 (sTape (nr := nrW) (sZ ta th))).val = 0 := rfl
  have hs : (Fin.castAdd 1 (sTape (nr := nrW) (sS ta th))).val = 4 := rfl
  have hp : (Fin.castAdd 1 (sTape (nr := nrW) (sPf ta th))).val = 6 := rfl
  funext j
  rw [frontBank_apply, hz, hs, hp]
  refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
  · rw [Fin.addCases_left, Fin.val_castAdd]
    rcases tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
    · rw [CheckedPCPP.coldBank_s, sTape_val]
      show (if i.val = 0 then RepairOrdinary.frame z else if i.val = 3 then s else if i.val = 5 then p else []) = _
      by_cases h0 : i.val = 0
      · rw [if_pos h0, if_pos h0, if_pos rfl]
      · rw [if_neg h0, if_neg h0, if_neg (by omega : i.val + 1 ≠ 0)]
        by_cases h3 : i.val = 3
        · rw [if_pos h3, if_pos (by omega : i.val + 1 = 4)]
        · rw [if_neg h3, if_neg (by omega : i.val + 1 ≠ 4)]
          by_cases h5 : i.val = 5
          · rw [if_pos h5, if_pos (by omega : i.val + 1 = 6)]
          · rw [if_neg h5, if_neg (by omega : i.val + 1 ≠ 6)]
    · rw [CheckedPCPP.coldBank_c, cTape_val]; simp
    · rw [CheckedPCPP.coldBank_r, rTape_val]
      unfold nsF
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  · rw [Fin.addCases_right, Fin.val_natAdd]
    unfold nsF
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end W3.NearCubicWires.RepairSource.Outer3.Front

namespace W3.NearCubicWires.RepairSource.Outer3

open Front

noncomputable def frontD (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
    (SV : Outer.SuccinctVerifier H G) : FrontSpecD mw SV :=
  let h := Classical.choice h2D_nonempty
  let K := Classical.choose (costF_le mw SV (OuterM.aRun mw SV) h)
  let e := Classical.choose (Classical.choose_spec (costF_le mw SV (OuterM.aRun mw SV) h))
  have hK := Classical.choose_spec (Classical.choose_spec (costF_le mw SV (OuterM.aRun mw SV) h))
  {
    t := nsF (OuterM.aRun mw SV).t h.t + 2 + nrW + 1
    st := (frontP mw SV (OuterM.aRun mw SV) h).size + 2
    M := Rewind.machine (frontP mw SV (OuterM.aRun mw SV) h).compile
    zIn := Fin.castAdd 1 (sTape (nr := nrW) (sZ (OuterM.aRun mw SV).t h.t))
    sIn := Fin.castAdd 1 (sTape (nr := nrW) (sS (OuterM.aRun mw SV).t h.t))
    pIn := Fin.castAdd 1 (sTape (nr := nrW) (sPf (OuterM.aRun mw SV).t h.t))
    field := Fin.castAdd 1 (sTape (nr := nrW) (sOUT (OuterM.aRun mw SV).t h.t))
    sizeSlot := Fin.castAdd 1 (sTape (nr := nrW) (sSZ (OuterM.aRun mw SV).t h.t))
    aritySlot := Fin.castAdd 1 (sTape (nr := nrW) (sAR (OuterM.aRun mw SV).t h.t))
    flag := Fin.castAdd 1 (sTape (nr := nrW) (sFL (OuterM.aRun mw SV).t h.t))
    inputs_nodup := by
      refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_singleton _⟩⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨Fin.ne_of_val_ne (by show (0 : ℕ) ≠ 4; decide), Fin.ne_of_val_ne (by show (0 : ℕ) ≠ 6; decide)⟩
      · simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact Fin.ne_of_val_ne (by show (4 : ℕ) ≠ 6; decide)
    fs := Fin.ne_of_val_ne (by show (7 : ℕ) ≠ 8; decide)
    fa := Fin.ne_of_val_ne (by show (7 : ℕ) ≠ 9; decide)
    sa := Fin.ne_of_val_ne (by show (8 : ℕ) ≠ 9; decide)
    K := K
    e := e
    onset := 1
    run := fun ν z B hν _ => by
      obtain ⟨τ, hx, hFL, hOUT, hSZ, hAR⟩ := front_run mw SV (OuterM.aRun mw SV) h ν hν z B
      obtain ⟨out, hr, hout⟩ := CheckedPCPP.WXExec.readyRewound hx (fun _ => rfl) (fun _ => rfl) rfl
      rw [bank_eqF] at hr
      -- the cost class
      obtain ⟨oA, hrA, -, -, -, hoW⟩ := (OuterM.aRun mw SV).run ν (Outer.width mw SV (2 ^ ν)) B.src
      have hdw := Dock.ready_len hrA ((PCPPNative.descriptor B.src).length + ν) (fun j => by
        unfold OuterM.aBank; split_ifs <;> simp) (OuterM.aRun mw SV).wOut
      rw [hoW] at hdw
      obtain ⟨oH, hrH, hoO, -, -⟩ := h.run (Outer.outC mw SV ν B.src) B.pf
      have hdc := Dock.ready_len hrH ((Outer.outC mw SV ν B.src).word.length + (PCPPNative.descriptor B.pf).length)
        (fun j => by unfold CheckedPCPP.portBank; split_ifs <;> simp) h.o
      rw [hoO, RepairOrdinary.frame_length] at hdc
      have hm : (Outer.Dat mw SV ν B).D.size ≤ (PCPPNative.descriptor (Outer.Dat mw SV ν B).D).length :=
        nodes_le_descriptor _
      have hcost := hK ν (PCPPNative.descriptor B.src).length (PCPPNative.descriptor B.pf).length
        (Outer.outC mw SV ν B.src).word.length (PCPPNative.descriptor (Outer.Dat mw SV ν B).D).length
        (Outer.width mw SV (2 ^ ν)) (Outer.Dat mw SV ν B).D.size (nu_lt_width mw SV ν) hdw (by
          have e1 : (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) =
              PCPPNative.descriptor (Outer.substCircuit (Outer.outC mw SV ν B.src).circuit B.pf).padToArity := rfl
          rw [e1]; omega) hm
      refine ⟨out, OuterM.readyRun_mono hr hcost, ?_, fun _ => ⟨?_, ?_, ?_⟩⟩
      · rw [hout, hFL]
      · rw [hout, hOUT]
      · rw [hout, hSZ]
      · rw [hout, hAR] }

theorem frontD_onset (mw : Outer.MWSource) {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {G : ℕ}
    (SV : Outer.SuccinctVerifier H G) : (frontD mw SV).onset = 1 := rfl

end W3.NearCubicWires.RepairSource.Outer3
