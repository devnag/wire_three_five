import W3.Recovery3.Case2Front

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)

namespace W3.NearCubicWires.RepairSource.Outer3.Case2

open Front

/-! ## The relabelled ready front -/

/-- The front's tape count (rewound compiled program). -/
noncomputable def T2 (h : H2D) : ℕ := ns2 UF.t h.t + 2 + nrW + 1

def perm2 (T : ℕ) (hT : 4 ≤ T) (j : Fin T) : Fin T :=
  ⟨if j.val = 1 then 3 else if j.val = 2 then 1 else if j.val = 3 then 2 else j.val, by
    have := j.isLt; split_ifs <;> omega⟩

theorem perm2_val (T : ℕ) (hT : 4 ≤ T) (j : Fin T) :
    (perm2 T hT j).val = if j.val = 1 then 3 else if j.val = 2 then 1 else if j.val = 3 then 2 else j.val := rfl

theorem perm2_inj (T : ℕ) (hT : 4 ≤ T) : Function.Injective (perm2 T hT) := by
  intro a b h
  have hv := congrArg Fin.val h
  rw [perm2_val, perm2_val] at hv
  apply Fin.ext
  split_ifs at hv <;> omega

theorem T2_ge (h : H2D) : 10 ≤ T2 h := by unfold T2 ns2; omega

theorem wi_eq {t : ℕ} (w : Fin 3 → List Bool) (j : Fin t) (k : Fin 3) (hj : j.val = k.val) :
    XorFamily.wordInput w j = w k := by
  unfold XorFamily.wordInput
  rw [dif_pos (by rw [hj]; exact k.isLt)]
  congr 1
  exact Fin.ext hj

theorem wi_nil {t : ℕ} (w : Fin 3 → List Bool) (j : Fin t) (hj : 3 ≤ j.val) : XorFamily.wordInput w j = [] := by
  unfold XorFamily.wordInput
  rw [dif_neg (by omega)]

noncomputable def M2 (h : H2D) :=
  RecoveryFocus.machine (perm2 (T2 h) (by have := T2_ge h; omega))
    (Rewind.machine (front2P h).compile)

/-- The relabelled tape of stream `i`. -/
noncomputable def p2 (h : H2D) (i : Fin (ns2 UF.t h.t + 1)) : Fin (T2 h) :=
  perm2 (T2 h) (by have := T2_ge h; omega) (Fin.castAdd 1 (WireExponent3_5.FinalPass.Tm.sTape (nr := nrW) i))

theorem p2_val (h : H2D) (k : ℕ) (hk : k < 8) :
    (p2 h (gx UF.t h.t k hk)).val = if k = 0 then 0 else if k = 1 then 1 else if k = 2 then 2 else k + 1 := by
  unfold p2
  rw [perm2_val]
  show (if (if k = 0 then 0 else k + 1) = 1 then 3 else if (if k = 0 then 0 else k + 1) = 2 then 1
    else if (if k = 0 then 0 else k + 1) = 3 then 2 else (if k = 0 then 0 else k + 1)) = _
  split_ifs <;> omega

theorem front2_ready (h : H2D) (oc : NearCubicWires.Bindings.MW20.OracleOutput) {q : ℕ} (B : BooleanCircuit q)
    (address : List Bool) :
    let Hc := (Outer.substCircuit oc.circuit B).padToArity
    ∃ out, ClockJoin.ReadyRun (M2 h)
        (2 * cost2 h oc.word.length (PCPPNative.descriptor B).length (PCPPNative.descriptor Hc).length q Hc.size + 2)
        (XorFamily.wordInput (t := T2 h) ![oc.word, RepairOrdinary.frame (PCPPNative.descriptor B),
          RepairOrdinary.frame address]) out ∧
      out (p2 h (tOUT UF.t h.t)) = RepairOrdinary.frame (PCPPNative.descriptor Hc) ∧
      out (p2 h (tSZ UF.t h.t)) = List.replicate Hc.size true ∧
      out (p2 h (tAR UF.t h.t)) = List.replicate q true ∧
      ∀ k : Fin 3, out ⟨k.val, by have := k.isLt; have := T2_ge h; omega⟩ =
        ![oc.word, RepairOrdinary.frame (PCPPNative.descriptor B), RepairOrdinary.frame address] k := by
  intro Hc
  have hT : 4 ≤ T2 h := by have := T2_ge h; omega
  obtain ⟨τ, hx, hW0, hFD, hFA, hOUT, hSZ, hAR⟩ := front2_run h oc B address
  obtain ⟨out0, hr, hout⟩ := CheckedPCPP.WXExec.readyRewound hx (fun _ => rfl) (fun _ => rfl) rfl
  set amb := XorFamily.wordInput (t := T2 h) ![oc.word, RepairOrdinary.frame (PCPPNative.descriptor B),
    RepairOrdinary.frame address] with hamb
  have hin : ∀ j, amb (perm2 (T2 h) hT j) =
      Fin.addCases (motive := fun _ => List Bool)
        (coldBank (start2 UF.t h.t oc.word (PCPPNative.descriptor B) address)) (fun _ : Fin 1 => []) j := by
    intro j
    refine Fin.addCases (fun j' => ?_) (fun j' => ?_) j
    · rw [Fin.addCases_left]
      rcases NearCubicWires.WireExponent3_5.PrimAsm.DockW.tape_cases j' with ⟨i, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [coldBank_s]
        show amb (perm2 (T2 h) hT (Fin.castAdd 1 (WireExponent3_5.FinalPass.Tm.sTape i))) =
          (if i.val = 0 then oc.word else if i.val = 1 then RepairOrdinary.frame (PCPPNative.descriptor B)
            else if i.val = 2 then RepairOrdinary.frame address else [])
        have hv : (perm2 (T2 h) hT (Fin.castAdd 1 (WireExponent3_5.FinalPass.Tm.sTape (nr := nrW) i))).val =
            if i.val = 0 then 0 else if i.val = 1 then 1 else if i.val = 2 then 2 else i.val + 1 := by
          rw [perm2_val]
          show (if (if i.val = 0 then 0 else i.val + 1) = 1 then 3 else if (if i.val = 0 then 0 else i.val + 1) = 2
            then 1 else if (if i.val = 0 then 0 else i.val + 1) = 3 then 2 else (if i.val = 0 then 0 else i.val + 1)) = _
          split_ifs <;> omega
        rw [hamb]
        by_cases h0 : i.val = 0
        · rw [wi_eq _ _ 0 (by rw [hv, if_pos h0]; rfl), if_pos h0]; rfl
        by_cases h1 : i.val = 1
        · rw [wi_eq _ _ 1 (by rw [hv, if_neg h0, if_pos h1]; rfl), if_neg h0, if_pos h1]; rfl
        by_cases h2 : i.val = 2
        · rw [wi_eq _ _ 2 (by rw [hv, if_neg h0, if_neg h1, if_pos h2]; rfl), if_neg h0, if_neg h1, if_pos h2]; rfl
        rw [wi_nil _ _ (by rw [hv, if_neg h0, if_neg h1, if_neg h2]; omega), if_neg h0, if_neg h1, if_neg h2]
      · rw [coldBank_c, hamb, wi_nil _ _ (by rw [perm2_val]; simp [WireExponent3_5.PrimAsm.DockW.cTape_val])]
      · rw [coldBank_r, hamb, wi_nil _ _ (by
          rw [perm2_val, Fin.val_castAdd, WireExponent3_5.PrimAsm.DockW.rTape_val]; unfold ns2; split_ifs <;> omega)]
    · rw [Fin.addCases_right, hamb, wi_nil _ _ (by rw [perm2_val, Fin.val_natAdd]; unfold ns2; split_ifs <;> omega)]
  have hf := hr.focus (perm2 (T2 h) hT) (perm2_inj (T2 h) hT) amb hin
  have hslot : ∀ i, install (perm2 (T2 h) hT) amb out0 (perm2 (T2 h) hT i) = out0 i := fun i =>
    install_slot _ (perm2_inj (T2 h) hT) _ _ i
  refine ⟨_, hf, (hslot _).trans ((hout _).trans hOUT), (hslot _).trans ((hout _).trans hSZ),
    (hslot _).trans ((hout _).trans hAR), ?_⟩
  intro k
  fin_cases k
  · exact (congrArg _ (Fin.ext (by rw [p2_val]; rfl) : (⟨0, _⟩ : Fin (T2 h)) = p2 h (tW0 UF.t h.t))).trans
      ((hslot _).trans ((hout _).trans hW0))
  · exact (congrArg _ (Fin.ext (by rw [p2_val]; rfl) : (⟨1, _⟩ : Fin (T2 h)) = p2 h (tFD UF.t h.t))).trans
      ((hslot _).trans ((hout _).trans hFD))
  · exact (congrArg _ (Fin.ext (by rw [p2_val]; rfl) : (⟨2, _⟩ : Fin (T2 h)) = p2 h (tFA UF.t h.t))).trans
      ((hslot _).trans ((hout _).trans hFA))

end W3.NearCubicWires.RepairSource.Outer3.Case2
