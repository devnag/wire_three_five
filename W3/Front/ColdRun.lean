import W3.Front.ColdDeep

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 400000

open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairSource
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicGates.Close NearCubicGates.Close.Platform
open NearCubicGates.Close.Setup NearCubicGates.Close.CheckedPCPP
open NearCubicWires.ExecutableInterfaces NearCubicWires.CanonicalWitnessCodec
open NearCubicWires.RepairOrdinary.RadixSemantics (value)

namespace W3.NearCubicWires.RepairSource.Outer3.Front

section Head
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

/-- The cold start: `frame x` on `X` (tape 2 of the compiled bank), `frame raw` on `RAW` (tape 3). -/
noncomputable def startC (x raw : List Bool) : WState (NSC mw SV F degree) nrW :=
  ⟨fun _ => 0, fun i => if i.val = 1 then RepairOrdinary.frame x else if i.val = 2 then RepairOrdinary.frame raw
    else [], fun _ => 0, false⟩

/-- The state after the head. -/
noncomputable def headState (n : ℕ) (x raw : List Bool) : WState (NSC mw SV F degree) nrW :=
  ((((startC mw SV F degree x raw).sets (cFL _ _ _ _) [false]).setv rN n).sets (cLEN _ _ _ _)
    (List.replicate n true)).sets (cORIG _ _ _ _) (RepairOrdinary.frame x)

theorem headState_st (n : ℕ) (x raw : List Bool) (i : Fin (NSC mw SV F degree + 1)) :
    (headState mw SV F degree n x raw).st i =
      if i.val = 1 then RepairOrdinary.frame x else if i.val = 2 then RepairOrdinary.frame raw
      else if i.val = 3 then List.replicate n true else if i.val = 4 then [false]
      else if i.val = 6 then RepairOrdinary.frame x else [] := by
  unfold headState startC
  simp only [WState.sets_st, WState.setv_st, Function.update_apply, Fin.ext_iff]
  by_cases h1 : i.val = 1 <;> by_cases h2 : i.val = 2 <;> by_cases h3 : i.val = 3 <;> by_cases h4 : i.val = 4 <;>
    by_cases h6 : i.val = 6 <;> simp [h1, h2, h3, h4, h6] <;> omega

theorem headState_val (n : ℕ) (x raw : List Bool) (r : Fin nrW) :
    (headState mw SV F degree n x raw).val r = if r = rN then n else 0 := by
  unfold headState startC
  simp only [WState.sets_val, WState.setv_val, Function.update_apply]

def headCost (n : ℕ) : ℕ := 200 * n + 200

theorem head_exec {n : ℕ} (x : BitInput n) (raw : List Bool) (cap : ℕ) (hcap : 4 * n + 4 ≤ cap)
    (P : WMX (NSC mw SV F degree) nrW) (τ : WState (NSC mw SV F degree) nrW) (m : ℕ)
    (hP : WXExec cap P (headState mw SV F degree n (List.ofFn x) raw) τ m) :
    WXExec cap (.seq (WMX.wr (cFL _ _ _ _) false) (.seq (BinW.width (cX _ _ _ _) rN tW)
        (.seq (TabMachine.writeOnes (cLEN _ _ _ _) rN rK2)
        (.seq (.wm (Codec.copyRW (cX _ _ _ _) (cORIG _ _ _ _) rOP rT rD)) P))))
      (startC mw SV F degree (List.ofFn x) raw) τ (headCost n + m) := by
  set σ0 := startC mw SV F degree (List.ofFn x) raw with hσ0
  have hxl : (List.ofFn x).length = n := List.length_ofFn
  have e1 : WXExec cap (WMX.wr (cFL _ _ _ _) false) σ0 (σ0.sets (cFL _ _ _ _) [false]) 1 := WXExec.wr cap _ false σ0
  set σ1 := σ0.sets (cFL _ _ _ _) [false] with hσ1
  have hnum : WireExponent3_5.SelectionMachine.Sort.NumOn σ1 (cX _ _ _ _) n (value (List.ofFn x)) := by
    refine ⟨?_, rfl⟩
    have hb := WireExponent3_5.CompilerMachine.Emit.binary_value_self (List.ofFn x)
    rw [hxl] at hb
    rw [hb]; rfl
  have e2 := BinW.width_spec cap (A := cX _ _ _ _) (K := rN) (T := tW) (by decide) n _ σ1 hnum rfl rfl (by omega)
  set σ2 := σ1.setv rN n with hσ2
  have e3 := TabMachine.writeOnes_spec cap (X := cLEN _ _ _ _) (K := rN) (K2 := rK2) (by decide) σ2 n rfl rfl
    (by simp [hσ2]) (by rw [hσ2, WState.setv_val, Function.update_of_ne (by decide)]; rfl) (by omega)
  set σ3 := σ2.sets (cLEN _ _ _ _) (List.replicate n true) with hσ3
  have e4 := Codec.copyRW_spec cap (cX _ _ _ _) (cORIG _ _ _ _) (by simp [Fin.ext_iff]) rOP rT rD (by decide)
    (by decide) (by decide) (List.ofFn x) [] σ3 (by rw [List.append_nil]; rfl) rfl rfl rfl
    (by rw [hσ3, WState.sets_val, hσ2, WState.setv_val, Function.update_of_ne (by decide)]; rfl)
    (by rw [hσ3, WState.sets_val, hσ2, WState.setv_val, Function.update_of_ne (by decide)]; rfl)
    (by rw [hσ3, WState.sets_val, hσ2, WState.setv_val, Function.update_of_ne (by decide)]; rfl) (by omega)
  rw [hxl] at e4
  exact WXExec.mono (WXExec.seq e1 (WXExec.seq e2 (WXExec.seq e3 (WXExec.seq (WXExec.wm e4) hP))))
    (by unfold headCost; omega)

end Head

section Cold
variable (mw : Outer.MWSource) {k0 : ℕ} {H0 : OrdinaryHierarchy (fun n => n ^ (k0 + 2))} {G0 : ℕ}
  (SV : Outer.SuccinctVerifier H0 G0) (F : FrontSpecD mw SV) (degree : ℕ)

noncomputable def deepCost (n : ℕ) (raw : List Bool) : ℕ :=
  prepCost n (Outer.width mw SV n) (OuterM.widthDonor mw SV).K (E0 degree) (fld1 raw) (fld2 raw) + 1 +
    tailU degree F.K F.e n (Outer.width mw SV n) (16 * Lq (E0 degree) (Outer.width mw SV n))

/-- The cold prefix's step bound. -/
noncomputable def coldU (cstar n : ℕ) (raw : List Bool) : ℕ :=
  headCost n + powCostP n + 30 * cstar + 25 * n + 100 + deepCost mw SV F degree n raw

/-- The cold prefix's register capacity. -/
noncomputable def capC (cstar n : ℕ) : ℕ := capD (E0 degree) n (Outer.width mw SV n) (cstar + n + 1)

theorem cold_exec_pow (cstar : ℕ) (h1c : 1 ≤ cstar) (honc : F.onset ≤ cstar) (ν : ℕ) (x : BitInput (2 ^ ν))
    (raw : List Bool) (h16 : 16 * raw.length ≤ 2 ^ ν) :
    ∃ τ, WXExec (capC mw SV degree cstar (2 ^ ν)) (coldP mw SV F degree cstar)
        (startC mw SV F degree (List.ofFn x) raw) τ (coldU mw SV F degree cstar (2 ^ ν) raw) ∧
      (∃ b : Bool, τ.st (cFL _ _ _ _) = [b] ∧ (b = true ↔ cstar ≤ ν ∧ PassCore mw SV degree ν x raw)) ∧
      τ.st (cLEN _ _ _ _) = List.replicate (2 ^ ν) true ∧ τ.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn x) ∧
      (∀ B : Outer.OuterGuess (Outer.width mw SV (2 ^ ν)), Worker.Decodes _ raw B → cstar ≤ ν →
        PassCore mw SV degree ν x raw →
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.field) =
          RepairOrdinary.frame (PCPPNative.descriptor (Outer.Dat mw SV ν B).D) ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.sizeSlot) =
          List.replicate (Outer.Dat mw SV ν B).D.size true ∧
        τ.st (mF (progB mw SV) (progU mw SV) (Dc degree) F F.aritySlot) =
          List.replicate (Outer.width mw SV (2 ^ ν)) true) := by
  classical
  have hcapd : capC mw SV degree cstar (2 ^ ν) =
      capD (E0 degree) (2 ^ ν) (Outer.width mw SV (2 ^ ν)) (cstar + 2 ^ ν + 1) := rfl
  obtain ⟨C1, C2, C3, C4, C5, C6⟩ := capD_facts (E0 degree) (2 ^ ν) (Outer.width mw SV (2 ^ ν)) (cstar + 2 ^ ν + 1)
  rw [← hcapd] at C1 C2 C3 C4 C5 C6
  set cap := capC mw SV degree cstar (2 ^ ν) with hcap
  have hνN : ν < 2 ^ ν := Nat.lt_two_pow_self
  set σ4 := headState mw SV F degree (2 ^ ν) (List.ofFn x) raw with hσ4
  have st4 := headState_st mw SV F degree (2 ^ ν) (List.ofFn x) raw
  have val4 := headState_val mw SV F degree (2 ^ ν) (List.ofFn x) raw
  -- P. `rNu := ν`, `FT := [true]`
  have eP := powP_exec (cap := cap) (cFT _ _ _ _) (2 ^ ν) σ4 (by rw [val4, if_pos rfl]) Nat.one_le_two_pow
    (by intro r hr; rw [val4]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact if_neg (by decide))
    (by rw [st4]; simp) rfl (by omega)
  have hpf : powFlag (2 ^ ν) = [true] := by unfold powFlag; rw [Nat.clog_pow 2 ν (by norm_num)]; simp
  rw [Nat.clog_pow 2 ν (by norm_num), hpf] at eP
  set σ5 := (σ4.setv rNu ν).sets (cFT _ _ _ _) [true] with hσ5
  have tFT : wbit σ5 (cFT _ _ _ _) = true := by
    unfold wbit; simp only [hσ5, WState.sets_st, WState.sets_sh, WState.setv_st, WState.setv_sh, Function.update_self]
    rfl
  -- G. `rC := c*`, `pF := [c* ≤ ν]`
  have v5C : σ5.val rC = 0 := by rw [hσ5, WState.sets_val, WState.setv_val, Function.update_of_ne (by decide), val4,
    if_neg (by decide)]
  have e6 := CheckedPCPP.NodeEmit.incN_spec (cap := cap) rC cstar σ5 (by rw [v5C]; omega)
  rw [v5C, Nat.zero_add] at e6
  set σ6 := σ5.setv rC cstar with hσ6
  have e7 := Recovery.HTParts.leW_exec cap (A := rC) (B := rNu) (U := pU) (K := pK) (T := pT) (F := pF) (by decide)
    cstar ν (by omega) σ6 (by simp [hσ6])
    (by rw [hσ6, WState.setv_val, Function.update_of_ne (by decide), hσ5, WState.sets_val, WState.setv_val,
      Function.update_self])
    (by rw [hσ6, WState.setv_val, Function.update_of_ne (by decide), hσ5, WState.sets_val, WState.setv_val,
      Function.update_of_ne (by decide), val4, if_neg (by decide)])
    (by rw [hσ6, WState.setv_val, Function.update_of_ne (by decide), hσ5, WState.sets_val, WState.setv_val,
      Function.update_of_ne (by decide), val4, if_neg (by decide)])
    (by rw [hσ6, WState.setv_val, Function.update_of_ne (by decide), hσ5, WState.sets_val, WState.setv_val,
      Function.update_of_ne (by decide), val4, if_neg (by decide)])
    (by rw [hσ6, WState.setv_val, Function.update_of_ne (by decide), hσ5, WState.sets_val, WState.setv_val,
      Function.update_of_ne (by decide), val4, if_neg (by decide)])
  set σ7 := σ6.setv pF (if cstar ≤ ν then 1 else 0) with hσ7
  have st7 : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 5 → σ7.st i = σ4.st i := fun i hi => by
    show Function.update σ4.st (cFT _ _ _ _) [true] i = _
    exact Function.update_of_ne (fun e => hi (by rw [e]; rfl)) _ _
  have sh7 : ∀ i : Fin (NSC mw SV F degree + 1), σ7.sh i = 0 := fun _ => rfl
  have val7 : ∀ r, r ≠ pF → r ≠ rC → r ≠ rNu → σ7.val r = σ4.val r := fun r h1 h2 h3 => by
    rw [hσ7, WState.setv_val, Function.update_of_ne h1, hσ6, WState.setv_val, Function.update_of_ne h2, hσ5,
      WState.sets_val, WState.setv_val, Function.update_of_ne h3]
  have hLEN7 : σ7.st (cLEN _ _ _ _) = List.replicate (2 ^ ν) true := by rw [st7 _ (by simp), st4]; simp
  have hX7 : σ7.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn x) := by rw [st7 _ (by simp), st4]; simp
  have hFL7 : σ7.st (cFL _ _ _ _) = [false] := by rw [st7 _ (by simp), st4]; simp
  by_cases hc : cstar ≤ ν
  · have tF : σ7.val pF ≠ 0 := by simp [hσ7, hc]
    obtain ⟨τ, eD, fl, facts, keep⟩ := deep_exec mw SV F degree ν (by omega) (by omega) x raw h16 cap
      (cstar + 2 ^ ν + 1) (le_of_eq hcapd.symm) σ7 hX7 (sh7 _)
      (by rw [st7 _ (by simp), st4]; simp) (sh7 _) hFL7 (sh7 _)
      (fun i hi => ⟨by rw [st7 i (by omega), st4, if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega), if_neg (by omega)], sh7 i⟩)
      (by rw [val7 _ (by decide) (by decide) (by decide), val4, if_pos rfl])
      (by intro r hr; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (rw [val7 _ (by decide) (by decide) (by decide), val4]; exact if_neg (by decide)))
    refine ⟨τ, WXExec.mono (head_exec mw SV F degree x raw cap (by omega) _ τ _
      (WXExec.ifrT (by rw [val4, if_pos rfl]; exact (Nat.two_pow_pos ν).ne')
        (WXExec.seq eP (WXExec.ifsT tFT (WXExec.seq (WXExec.wm e6) (WXExec.seq e7 (WXExec.ifrT tF eD)))))))
      (by unfold coldU deepCost; omega), ?_, ?_, ?_, ?_⟩
    · obtain ⟨b, hb, hiff⟩ := fl
      exact ⟨b, hb, by rw [hiff]; exact ⟨fun h => ⟨hc, h⟩, fun h => h.2⟩⟩
    · rw [keep _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hLEN7
    · rw [keep _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hX7
    · intro B hB _ hP; exact facts B hB hP
  · have tF : σ7.val pF = 0 := by simp [hσ7, hc]
    refine ⟨σ7, WXExec.mono (head_exec mw SV F degree x raw cap (by omega) _ σ7 _
      (WXExec.ifrT (by rw [val4, if_pos rfl]; exact (Nat.two_pow_pos ν).ne')
        (WXExec.seq eP (WXExec.ifsT tFT (WXExec.seq (WXExec.wm e6) (WXExec.seq e7
          (WXExec.ifrF tF (WXExec.skip cap σ7))))))))
      (by unfold coldU deepCost; omega), ⟨false, hFL7, ⟨fun h => absurd h (by decide), fun h => absurd h.1 hc⟩⟩,
      hLEN7, hX7, fun _ _ h => absurd h hc⟩

theorem cold_exec_rej (cstar : ℕ) {n : ℕ} (hn : ∀ ν, n ≠ 2 ^ ν) (x : BitInput n) (raw : List Bool) :
    ∃ τ, WXExec (capC mw SV degree cstar n) (coldP mw SV F degree cstar)
        (startC mw SV F degree (List.ofFn x) raw) τ (coldU mw SV F degree cstar n raw) ∧
      τ.st (cFL _ _ _ _) = [false] ∧
      τ.st (cLEN _ _ _ _) = List.replicate n true ∧ τ.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn x) := by
  classical
  have hcapd : capC mw SV degree cstar n = capD (E0 degree) n (Outer.width mw SV n) (cstar + n + 1) := rfl
  obtain ⟨C1, C2, C3, C4, C5, C6⟩ := capD_facts (E0 degree) n (Outer.width mw SV n) (cstar + n + 1)
  rw [← hcapd] at C1 C2 C3 C4 C5 C6
  set cap := capC mw SV degree cstar n with hcap
  set σ4 := headState mw SV F degree n (List.ofFn x) raw with hσ4
  have st4 := headState_st mw SV F degree n (List.ofFn x) raw
  have val4 := headState_val mw SV F degree n (List.ofFn x) raw
  have hLEN4 : σ4.st (cLEN _ _ _ _) = List.replicate n true := by rw [st4]; simp
  have hX4 : σ4.st (cX _ _ _ _) = RepairOrdinary.frame (List.ofFn x) := by rw [st4]; simp
  have hFL4 : σ4.st (cFL _ _ _ _) = [false] := by rw [st4]; simp
  by_cases h0 : n = 0
  · refine ⟨σ4, WXExec.mono (head_exec mw SV F degree x raw cap (by omega) _ σ4 _
      (WXExec.ifrF (by rw [val4, if_pos rfl]; exact h0) (WXExec.skip cap σ4))) (by unfold coldU; omega),
      hFL4, hLEN4, hX4⟩
  have eP := powP_exec (cap := cap) (cFT _ _ _ _) n σ4 (by rw [val4, if_pos rfl]) (by omega)
    (by intro r hr; rw [val4]; simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact if_neg (by decide))
    (by rw [st4]; simp) rfl (by omega)
  have hpf : powFlag n = [] := by
    unfold powFlag
    rw [if_neg]
    intro h
    exact hn _ (le_antisymm (Nat.le_pow_clog (by norm_num) n) h)
  rw [hpf] at eP
  set σ5 := (σ4.setv rNu (Nat.clog 2 n)).sets (cFT _ _ _ _) [] with hσ5
  have tFT : wbit σ5 (cFT _ _ _ _) = false := by unfold wbit; simp [hσ5]; rfl
  have st5 : ∀ i : Fin (NSC mw SV F degree + 1), i.val ≠ 5 → σ5.st i = σ4.st i := fun i hi => by
    show Function.update σ4.st (cFT _ _ _ _) [] i = _
    exact Function.update_of_ne (fun e => hi (by rw [e]; rfl)) _ _
  refine ⟨σ5, WXExec.mono (head_exec mw SV F degree x raw cap (by omega) _ σ5 _
      (WXExec.ifrT (by rw [val4, if_pos rfl]; exact h0) (WXExec.seq eP (WXExec.ifsF tFT (WXExec.skip cap σ5)))))
      (by unfold coldU; omega), ?_, ?_, ?_⟩
  · rw [st5 _ (by simp)]; exact hFL4
  · rw [st5 _ (by simp)]; exact hLEN4
  · rw [st5 _ (by simp)]; exact hX4

end Cold

end W3.NearCubicWires.RepairSource.Outer3.Front
