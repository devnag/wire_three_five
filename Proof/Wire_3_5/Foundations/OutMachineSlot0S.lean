import Proof.Wire_3_5.Foundations.OutMachineSlot0T

/-! # SA's slot 0, part 3: the trim's run

* `cntK` (one copy of `|fpIn|`), `cnt10_spec`, `rewK` (one rewind by a copy);
* **`trim_spec`**: from `frame (r.word ++ sfx)` on `I0` (everything else blank), `T0 = frame r.word`, the input
  kept, the scratch within `2|fpIn|+1`, every other stream blank, heads and registers `0`, within
  `3000·(|fpIn|+1)^2` steps at any capacity `≥ 28·(|fpIn|+1)`.

Paper quantity of the main type: the request word inside the final pass's input (P3:3165-3175). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimT
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront (GLt gInP gOutP)
open NearCubicWires.WireExponent3_5.PrimT.FlipsPack (flD)
open NearCubicWires.WireExponent3_5.FinalPass.Out.ReqSkip
open NearCubicWires.RepairOrdinary.Streaming (marks marks_append marks_length)

theorem R_ne_k (i : ℕ) (h : i < 10) : R0 ≠ kk i h := fun e => by
  have := congrArg Fin.val e; simp [R0, kk] at this; omega

/-- One copy of `|w|`. -/
theorem cntK (cap L : ℕ) (w : List Bool) (hL : w.length = L) (i : ℕ) (h : i < 10) (sh : Fin (S0ns + 1) → ℕ)
    (st : Fin (S0ns + 1) → List Bool) (cell : Bool) (hA : st I0 = frame w) (hh : sh I0 = 0) (hc : 2 * L ≤ cap) :
    WExec cap (P1.cntW I0 R0 (kk i h)) ⟨sh, st, Vt L 0 0 i, cell⟩ ⟨sh, st, Vt L 0 0 (i + 1), cell⟩
      (27 * w.length + 3) := by
  refine WExec.cast cap (CarKit.cntF_spec cap I0 R0 (kk i h) (R_ne_k i h) w ⟨sh, st, Vt L 0 0 i, cell⟩ hA hh
    (Vt_R L 0 0 i) (by simp only [Vt, kk]; split_ifs <;> omega) (by omega)) ?_ le_rfl
  show (⟨sh, st, Function.update (Vt L 0 0 i) (kk i h) w.length, cell⟩ : WState S0ns 17) = _
  rw [hL, Vt_fill L 0 0 i h (by omega)]

theorem cnt10_spec (cap L : ℕ) (w : List Bool) (hL : w.length = L) (sh : Fin (S0ns + 1) → ℕ)
    (st : Fin (S0ns + 1) → List Bool) (cell : Bool) (hA : st I0 = frame w) (hh : sh I0 = 0) (hc : 2 * L ≤ cap) :
    WExec cap cnt10 ⟨sh, st, Vt L 0 0 0, cell⟩ ⟨sh, st, Vt L 0 0 10, cell⟩ (10 * (27 * w.length + 3) + 9) := by
  refine WExec.mono (WExec.seq (cntK cap L w hL 0 (by omega) sh st cell hA hh hc) (WExec.seq
    (cntK cap L w hL 1 (by omega) sh st cell hA hh hc) (WExec.seq (cntK cap L w hL 2 (by omega) sh st cell hA hh hc)
    (WExec.seq (cntK cap L w hL 3 (by omega) sh st cell hA hh hc) (WExec.seq (cntK cap L w hL 4 (by omega) sh st cell hA hh hc)
    (WExec.seq (cntK cap L w hL 5 (by omega) sh st cell hA hh hc) (WExec.seq (cntK cap L w hL 6 (by omega) sh st cell hA hh hc)
    (WExec.seq (cntK cap L w hL 7 (by omega) sh st cell hA hh hc) (WExec.seq (cntK cap L w hL 8 (by omega) sh st cell hA hh hc)
    (cntK cap L w hL 9 (by omega) sh st cell hA hh hc)))))))))) (by omega)

/-- One rewind of `X` by the next copy of `L`. -/
theorem rewK (cap L m lo hi : ℕ) (h : lo < 10) (hlo : lo < hi) (X : Fin (S0ns + 1)) (σ : WState S0ns 17)
    (hv : σ.val = Vt L m lo hi) (hc : L ≤ cap) :
    WExec cap (WM.rewind X (kk lo h)) σ ((σ.setv (kk lo h) 0).seth X (σ.sh X - L)) (5 * L + 1) ∧
      ((σ.setv (kk lo h) 0).seth X (σ.sh X - L)).val = Vt L m (lo + 1) hi := by
  refine ⟨wrewind_spec cap X (kk lo h) L σ (by rw [hv]; exact Vt_k L m lo hi lo h le_rfl hlo)
    (by rw [hv, Vt_k L m lo hi lo h le_rfl hlo]; exact hc), ?_⟩
  rw [WState.seth_val, WState.setv_val, hv, Vt_use L m lo hi h]

theorem T_ne_I : T0 ≠ I0 := gs_ne_I _
theorem T_ne_U : T0 ≠ U0 := gs_ne_U _

/-- **The trim's run.** -/
theorem trim_spec (cap : ℕ) (r : PrimRequest) (sfx : List Bool) (σ : WState S0ns 17)
    (hI : σ.st I0 = frame (r.word ++ sfx)) (hbl : ∀ i, i ≠ I0 → σ.st i = []) (hsh : ∀ i, σ.sh i = 0)
    (hv : ∀ q, σ.val q = 0) (hcap : 28 * ((r.word ++ sfx).length + 1) ≤ cap) :
    ∃ (τ : WState S0ns 17) (n : ℕ), WExec cap trimP σ τ n ∧ n ≤ 3000 * ((r.word ++ sfx).length + 1) ^ 2 ∧
      τ.st I0 = σ.st I0 ∧ τ.st T0 = frame r.word ∧ (τ.st U0).length ≤ 2 * (r.word ++ sfx).length + 1 ∧
      (∀ i, i ≠ I0 → i ≠ U0 → i ≠ T0 → τ.st i = []) ∧ (∀ i, τ.sh i = 0) ∧ (∀ q, τ.val q = 0) := by
  set w := r.word ++ sfx with hw
  set L := w.length with hL
  have hLs : L = r.word.length + sfx.length := by rw [hL, hw, List.length_append]
  have hmk : frame w = marks r.word ++ (marks sfx ++ [false]) := by
    rw [Slot1.frame_marks, hw, marks_append, List.append_assoc]
  have hr1 := Slot1.word_pos r
  have hfl : (frame w).length = 2 * L + 1 := by rw [Slot1.frame_length]
  -- 1. ten copies of `L`
  have hσ0 : σ = ⟨σ.sh, σ.st, Vt L 0 0 0, σ.cell⟩ :=
    WState.eq rfl rfl (by rw [Vt_start]; funext q; exact hv q) rfl
  have s1 := cnt10_spec cap L w rfl σ.sh σ.st σ.cell hI (hsh I0) (by omega)
  rw [← hσ0] at s1
  set σ1 : WState S0ns 17 := ⟨σ.sh, σ.st, Vt L 0 0 10, σ.cell⟩ with hσ1
  -- 2. the input frame to the scratch
  obtain ⟨σ2, s2, e2U, e2Uh, e2I, e2Ih, o2, v2, -⟩ := CarWM.copyFrame_spec cap I0 U0 I_ne_U [] w [] σ1
    (by simp [hσ1, hI]) (by simp [hσ1, hsh]) (by simp [hσ1, hsh, hbl U0 (Ne.symm I_ne_U)])
  have v2' : σ2.val = Vt L 0 0 10 := by rw [v2]
  -- 3. the input rewound
  obtain ⟨s3, v3⟩ := rewK cap L 0 0 10 (by omega) (by omega) I0 σ2 v2' (by omega)
  set σ3 := (σ2.setv (kk 0 (by omega)) 0).seth I0 (σ2.sh I0 - L) with hσ3
  obtain ⟨s4, v4⟩ := rewK cap L 0 1 10 (by omega) (by omega) I0 σ3 v3 (by omega)
  set σ4 := (σ3.setv (kk 1 (by omega)) 0).seth I0 (σ3.sh I0 - L) with hσ4
  -- 4. the scratch rewound
  obtain ⟨s5, v5⟩ := rewK cap L 0 2 10 (by omega) (by omega) U0 σ4 v4 (by omega)
  set σ5 := (σ4.setv (kk 2 (by omega)) 0).seth U0 (σ4.sh U0 - L) with hσ5
  obtain ⟨s6, v6⟩ := rewK cap L 0 3 10 (by omega) (by omega) U0 σ5 v5 (by omega)
  set σ6 := (σ5.setv (kk 3 (by omega)) 0).seth U0 (σ5.sh U0 - L) with hσ6
  have s7 := WExec.bwd (cap := cap) U0 σ6
  set σ7 := σ6.seth U0 (σ6.sh U0 - 1) with hσ7
  have h7U : σ7.st U0 = frame w ∧ σ7.sh U0 = 0 := by
    refine ⟨by simp only [hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_st, WState.setv_st]; rw [e2U]; simp [hσ1, hbl U0
      (Ne.symm I_ne_U)], ?_⟩
    simp only [hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_sh, WState.setv_sh, Function.update_self,
      Function.update_of_ne (Ne.symm I_ne_U)]
    rw [e2Uh, e2U]; simp [hσ1, hbl U0 (Ne.symm I_ne_U), hfl]; omega
  have v7 : σ7.val = Vt L 0 4 10 := by rw [hσ7, WState.seth_val, v6]
  -- 5. the request word skipped on the scratch
  have r8 := reqSkip_spec cap U0 f0 c0 v0 p0 t0 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) M0 (by decide) (by decide) (by decide) (by decide)
    (by decide) r (marks sfx ++ [false]) σ7 (by rw [h7U.1, hmk]) h7U.2
    (by rw [v7]; exact Vt_low L 0 4 10 f0 (by decide)) (by rw [v7]; exact Vt_low L 0 4 10 c0 (by decide))
    (by rw [v7]; exact Vt_low L 0 4 10 v0 (by decide)) (by rw [v7]; exact Vt_low L 0 4 10 p0 (by decide))
    (by rw [v7]; exact Vt_low L 0 4 10 t0 (by decide)) (by rw [v7]; exact Vt_Mv L 0 4 10)
    (reqCaps_of cap r (by omega))
  set mb := if PrimAsm.Codec.modeBit r.mode then 1 else 0 with hmb
  set σ8 := (σ7.seth U0 (2 * r.word.length)).setv M0 mb with hσ8
  have v8 : σ8.val = Vt L mb 4 10 := by rw [hσ8, WState.setv_val, WState.seth_val, v7, Vt_M]
  -- 6. the request word's frame closed
  have s9 := WExec.wr (cap := cap) U0 false σ8
  obtain ⟨old, tl, hot⟩ : ∃ old tl, marks sfx ++ [false] = old :: tl := by
    cases h : marks sfx ++ [false] with
    | nil => simp at h
    | cons x y => exact ⟨x, y, rfl⟩
  set σ9 := σ8.sets U0 (writeTapeBit (σ8.st U0) (σ8.sh U0) false) with hσ9
  have h9U : σ9.st U0 = frame r.word ++ tl ∧ σ9.sh U0 = 2 * r.word.length := by
    have e8 : σ8.st U0 = marks r.word ++ old :: tl := by
      simp only [hσ8, WState.setv_st, WState.seth_st]; rw [h7U.1, hmk, hot]
    have e8h : σ8.sh U0 = (marks r.word).length := by
      simp only [hσ8, WState.setv_sh, WState.seth_sh, Function.update_self, marks_length]
    refine ⟨?_, ?_⟩
    · simp only [hσ9, WState.sets_st, Function.update_self]
      rw [e8, e8h, writeTapeBit_mid, Slot1.frame_marks, List.append_assoc]; rfl
    · simp only [hσ9, WState.sets_sh]; rw [e8h, marks_length]
  have v9 : σ9.val = Vt L mb 4 10 := by rw [hσ9, WState.sets_val, v8]
  -- 7. the scratch rewound
  obtain ⟨s10, v10⟩ := rewK cap L mb 4 10 (by omega) (by omega) U0 σ9 v9 (by omega)
  set σ10 := (σ9.setv (kk 4 (by omega)) 0).seth U0 (σ9.sh U0 - L) with hσ10
  obtain ⟨s11, v11⟩ := rewK cap L mb 5 10 (by omega) (by omega) U0 σ10 v10 (by omega)
  set σ11 := (σ10.setv (kk 5 (by omega)) 0).seth U0 (σ10.sh U0 - L) with hσ11
  have h11U : σ11.st U0 = [] ++ (frame r.word ++ tl) ∧ σ11.sh U0 = 0 := by
    refine ⟨by simp only [hσ11, hσ10, WState.seth_st, WState.setv_st]; rw [h9U.1]; rfl, ?_⟩
    simp only [hσ11, hσ10, WState.seth_sh, WState.setv_sh, Function.update_self]
    rw [h9U.2]; omega
  -- the request port blank so far
  have hT11 : σ11.st T0 = [] ∧ σ11.sh T0 = 0 := by
    have hT2 := o2 T0 T_ne_I T_ne_U
    refine ⟨?_, ?_⟩
    · simp only [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_st, WState.setv_st, WState.sets_st,
        Function.update_of_ne T_ne_U]
      rw [hT2.1]; simp [hσ1, hbl T0 T_ne_I]
    · simp only [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_sh, WState.setv_sh, WState.sets_sh,
        Function.update_of_ne T_ne_U, Function.update_of_ne T_ne_I]
      rw [hT2.2]; simp [hσ1, hsh]
  -- 8. the request word's frame to the request port
  obtain ⟨σ12, s12, e12T, e12Th, e12U, e12Uh, o12, v12, -⟩ := CarWM.copyFrame_spec cap U0 T0 (Ne.symm T_ne_U) []
    r.word tl σ11 h11U.1 h11U.2 (by rw [hT11.1, hT11.2]; rfl)
  have v12' : σ12.val = Vt L mb 6 10 := by rw [v12, v11]
  -- 9. the scratch and the port rewound
  obtain ⟨s13, v13⟩ := rewK cap L mb 6 10 (by omega) (by omega) U0 σ12 v12' (by omega)
  set σ13 := (σ12.setv (kk 6 (by omega)) 0).seth U0 (σ12.sh U0 - L) with hσ13
  obtain ⟨s14, v14⟩ := rewK cap L mb 7 10 (by omega) (by omega) U0 σ13 v13 (by omega)
  set σ14 := (σ13.setv (kk 7 (by omega)) 0).seth U0 (σ13.sh U0 - L) with hσ14
  obtain ⟨s15, v15⟩ := rewK cap L mb 8 10 (by omega) (by omega) T0 σ14 v14 (by omega)
  set σ15 := (σ14.setv (kk 8 (by omega)) 0).seth T0 (σ14.sh T0 - L) with hσ15
  obtain ⟨s16, v16⟩ := rewK cap L mb 9 10 (by omega) (by omega) T0 σ15 v15 (by omega)
  set σ16 := (σ15.setv (kk 9 (by omega)) 0).seth T0 (σ15.sh T0 - L) with hσ16
  have s17 := WExec.bwd (cap := cap) T0 σ16
  set σ17 := σ16.seth T0 (σ16.sh T0 - 1) with hσ17
  -- 10. the mode flag cleared
  obtain ⟨τ, s18, eτst, eτsh, vτ⟩ : ∃ τ, WExec cap (.ifr M0 (.dec M0) .skip) σ17 τ 3 ∧ τ.st = σ17.st ∧
      τ.sh = σ17.sh ∧ τ.val = Vt L 0 10 10 := by
    have hv17 : σ17.val = Vt L mb 10 10 := by rw [hσ17, WState.seth_val, v16]
    by_cases hm : PrimAsm.Codec.modeBit r.mode = true
    · have hmb' : mb = 1 := by rw [hmb, if_pos hm]
      have hne : σ17.val M0 ≠ 0 := by rw [hv17, Vt_Mv, hmb']; exact one_ne_zero
      have d1 := WExec.dec (cap := cap) M0 σ17 (by rw [hv17, Vt_Mv, hmb']; omega)
      refine ⟨_, WExec.mono (WExec.ifrT hne d1) (by omega), rfl, rfl, ?_⟩
      rw [WState.setv_val, hv17, Vt_Mv, Vt_M, hmb']
    · have hmb' : mb = 0 := by rw [hmb, if_neg hm]
      have hz : σ17.val M0 = 0 := by rw [hv17, Vt_Mv, hmb']
      exact ⟨σ17, WExec.mono (WExec.ifrF hz (WExec.skip σ17)) (by omega), rfl, rfl, by rw [hv17, hmb']⟩
  -- the facts
  have hTst : σ17.st T0 = frame r.word := by
    simp only [hσ17, hσ16, hσ15, hσ14, hσ13, WState.seth_st, WState.setv_st]
    rw [e12T, hT11.1]; rfl
  have hUst : σ17.st U0 = frame r.word ++ tl := by
    simp only [hσ17, hσ16, hσ15, hσ14, hσ13, WState.seth_st, WState.setv_st]
    rw [e12U, h11U.1]; rfl
  have hIst : σ17.st I0 = σ.st I0 := by
    have hI12 := o12 I0 I_ne_U (Ne.symm T_ne_I)
    simp only [hσ17, hσ16, hσ15, hσ14, hσ13, WState.seth_st, WState.setv_st]
    rw [hI12.1]
    simp only [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_st, WState.setv_st, WState.sets_st,
      Function.update_of_ne I_ne_U]
    rw [e2I]
  have htl0 : tl.length = 2 * sfx.length := by
    have h1 : (marks sfx ++ [false]).length = (old :: tl).length := by rw [hot]
    rw [List.length_append, marks_length, List.length_singleton, List.length_cons] at h1
    omega
  have htl : (frame r.word ++ tl).length = 2 * L + 1 := by
    rw [List.length_append, Slot1.frame_length, htl0, hLs]; ring
  refine ⟨τ, _, WExec.seq s1 (WExec.seq s2 (WExec.seq s3 (WExec.seq s4 (WExec.seq s5 (WExec.seq s6 (WExec.seq s7
    (WExec.seq r8 (WExec.seq s9 (WExec.seq s10 (WExec.seq s11 (WExec.seq s12 (WExec.seq s13 (WExec.seq s14
      (WExec.seq s15 (WExec.seq s16 (WExec.seq s17 s18)))))))))))))))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hq := Slot1.reqCost_le r L (by omega)
    have := Slot1.frame_length r.word
    nlinarith
  · rw [eτst, hIst]
  · rw [eτst, hTst]
  · rw [eτst, hUst, htl]
  · intro i h1 h2 h3
    rw [eτst]
    have hi2 := o2 i h1 h2
    have hi12 := o12 i h2 h3
    simp only [hσ17, hσ16, hσ15, hσ14, hσ13, WState.seth_st, WState.setv_st]
    rw [hi12.1]
    simp only [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_st, WState.setv_st, WState.sets_st,
      Function.update_of_ne h2]
    rw [hi2.1]; simp [hσ1, hbl i h1]
  · intro i
    rw [eτsh]
    by_cases hiT : i = T0
    · subst hiT
      simp only [hσ17, hσ16, hσ15, WState.seth_sh, WState.setv_sh, Function.update_self]
      simp only [hσ14, hσ13, WState.seth_sh, WState.setv_sh, Function.update_of_ne T_ne_U]
      rw [e12Th, e12T, hT11.1]; simp [Slot1.frame_length]; omega
    · simp only [hσ17, hσ16, hσ15, WState.seth_sh, WState.setv_sh, Function.update_of_ne hiT]
      by_cases hiU : i = U0
      · subst hiU
        simp only [hσ14, hσ13, WState.seth_sh, WState.setv_sh, Function.update_self]
        rw [e12Uh]; simp only [List.length_nil, Nat.zero_add]; omega
      · simp only [hσ14, hσ13, WState.seth_sh, WState.setv_sh, Function.update_of_ne hiU]
        by_cases hiI : i = I0
        · subst hiI
          rw [(o12 I0 I_ne_U (Ne.symm T_ne_I)).2]
          simp only [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_sh, WState.setv_sh, WState.sets_sh,
            Function.update_of_ne I_ne_U, Function.update_self]
          rw [e2Ih]; simp only [List.length_nil, Nat.zero_add]; omega
        · rw [(o12 i hiU hiT).2]
          simp only [hσ11, hσ10, hσ9, hσ8, hσ7, hσ6, hσ5, hσ4, hσ3, WState.seth_sh, WState.setv_sh, WState.sets_sh,
            Function.update_of_ne hiU, Function.update_of_ne hiI]
          rw [(o2 i hiI hiU).2]; simp [hσ1, hsh]
  · intro q; rw [vτ, Vt_zero]

end NearCubicWires.WireExponent3_5.FinalPass.Out.Slot0
