import Proof.Wire_3_5.Primitive.SeedFix.C4GateSymB
import Proof.Wire_3_5.Primitive.Writers.ThrDataIface2

/-! # G3, the THR gate-frame writer, part 1: the stages and the run (P3:1655-1664, 3119-3120)

"The algorithm receives polynomial-bit integer circuit descriptions" (P3:3119-3120); a THR call's pool is
`Records.thrPool P Cs carriers` (each carrier's doubled atoms, then the tuple's bottom occurrences).
The THR gate writer is G2's writer with the THR data stage (`ThrData.ThrDataStage2`: the tuple's one
table on `tabS`, blank when `a' = 0`) in place of the SYM stage, and the converter over the slots `[0, 1, 2]` (the two
carrier slots, then the tuple's table on `tabStream 2 = sSym 0 3`):

* `data_stageM` (any stage on `Data`'s layout, docked on `dS`), **`conv_stageJ`** (the converter over any listed slots);
* `gtM D Dv Cv`; the slots `gtG`/`gtH`/`gtHs`; **`thrPool_eq`** (the pool is the three slots, `thrOccs_gates`);
  `slot_T3`, `slot_H3`;
* **`gt_run`**: `WriterRun (gtM D Dv Cv) Bud (gsIn Dv) (gsOut Dv) (Data.reqW P.n true (thrCodes Cs) (carriers.map code) tl)
  (C4Geo.gateField (Records.thrPool P Cs carriers))` under the stage's hypotheses at `L = W = value Dv Cv P.n`.

Paper quantity of the main type: C3a's gate field of the THR call's pool. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimT.C4GateSym
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm.GeoFront NearCubicWires.SupplierPipeline

/-! ## Generic stages -/

section Gen
variable {Dv : ℕ}

/-- **Any data stage on `Data`'s layout**, docked on `dS`. -/
theorem data_stageM {s : ℕ} (M : Machine DT s) (E : Fin (GT Dv) → List Bool) (w : List Bool) (n W N m : ℕ)
    (tout : Fin (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) → List Bool)
    (h : Step M N (fun _ => 0)
      (Fin.addCases (PrimAsm.Data.rawIn w n W W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => 0)
      (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)))
    (h0 : E (gl (ws gIN)) = frame w) (h2 : E (gl (ws gNT)) = List.replicate n true)
    (h3 : E (dReg (dPos PrimAsm.Data.sLT)) = List.replicate W true) (h4 : E (gl (ws gCT)) = List.replicate W true)
    (hz : ∀ d : Fin DT, d.val ≠ 3 → E (dReg d) = []) :
    Step (RecoveryFocus.machine (dS (Dv := Dv)) M) N (fun _ => 0) E (fun _ => 0)
      (install dS E (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))) :=
  dockZ h dS dS_inj (fun _ => 0) E (fun _ => rfl) (data_entry E w n W h0 h2 h3 h4 hz)

/-- **The converter over the listed slots `js`**, docked on `cS`: C3a's gate field on the output tape. -/
theorem conv_stageJ (js : List (Fin 6)) (hnd : js.Nodup) (E : Fin (GT Dv) → List Bool) (n H : ℕ)
    (Gs : Fin 6 → List (NormalizedThresholdGate n)) (hs : Fin 6 → ℕ)
    (hns : E (cReg nsPos) = List.replicate n true)
    (hz : ∀ x : Fin 34, x.val ≠ 11 → E (cReg x) = [])
    (hT : ∀ j ∈ js, E (dReg (dPos (tabStream j))) = FinalPass.Corner.gatesW (hs j) (Gs j) ∨
      (E (dReg (dPos (tabStream j))) = [] ∧ Gs j = []))
    (hH : ∀ j ∈ js, 1 ≤ hs j ∧ hs j ≤ H ∧ ∀ g ∈ Gs j, C4Gates.GB (hs j) g) :
    ∃ E' : Fin (GT Dv) → List Bool,
      Step (RecoveryFocus.machine (cS (Dv := Dv))
          (MaskedReset.machine (C4Gates.convAll js).toProg.compile (fun _ => true)))
        (2 * C4Gates.convCost n (js.flatMap Gs).length H + 2) (fun _ => 0) E (fun _ => 0) E' ∧
      E' (cReg 0) = C4Geo.gateField (js.flatMap Gs) ∧ ∀ i : Fin (GT Dv), i.val < GLt Dv → E' i = E i := by
  have hsO : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sO)) =
      cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sO)) := cS_other _ (by decide)
  have hsS : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sS)) =
      cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sS)) := cS_other _ (by decide)
  have hsQ : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sNQ)) =
      cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sNQ)) := cS_other _ (by decide)
  have hsT : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sTS)) =
      cReg (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sTS)) := cS_other _ (by decide)
  have hsN : cS (Dv := Dv) nsPos = cReg nsPos := cS_other _ (by decide)
  have hE : ∀ j : Fin 34, (∀ i, j ≠ Fin.castAdd 1 (sTape (ns := 11) (nr := 20) i)) → E (cS j) = [] := by
    intro j hj
    have j0 : j.val ≠ 0 := fun h => hj 0 (Fin.ext (by rw [h]; rfl))
    have jm : ¬(2 ≤ j.val ∧ j.val ≤ 12) := fun ⟨a, b⟩ => hj ⟨j.val - 1, by omega⟩
      (Fin.ext (by show j.val = if j.val - 1 = 0 then 0 else j.val - 1 + 1; split_ifs <;> omega))
    rw [cS_other j (by omega)]
    exact hz j (by omega)
  obtain ⟨τ, c, hx, hc, hO⟩ := C4Gates.convAll_spec2
    (2 * (((js.flatMap Gs).length + 1) * ((8 * H + 8) * (n + 2) + 8 * natBitLength n + 8)) +
      8 * n + 8 * natBitLength n + 8 * natBitLength (js.flatMap Gs).length + 2 * H + 100) (by omega)
    H Gs hs js hnd (stOf (ns := 11) (nr := 20) cS E) (fun _ => rfl) (fun _ => rfl)
    (by rw [stOf_st]; show E (cS nsPos) = _; rw [hsN, hns])
    (by rw [stOf_st, hsO]; exact hz _ (by decide))
    (by rw [stOf_st, hsS]; exact hz _ (by decide))
    (by rw [stOf_st, hsQ]; exact hz _ (by decide))
    (by rw [stOf_st, hsT]; exact hz _ (by decide))
    (fun j hj => by rw [stOf_st, cS_tbl]; exact hT j hj) hH (le_refl _)
  obtain ⟨A', s, hA'⟩ := dock_wm _ c (C4Gates.convAll js) cS cS_inj E hE τ c hx (le_refl c)
  have e0 : cS (Dv := Dv) (Fin.castAdd 1 (sTape (nr := 20) C4Gates.sO)) = cReg 0 := by
    rw [hsO]; exact congrArg cReg (Fin.ext rfl)
  refine ⟨_, s.enlarge (by omega), ?_, fun i hi => install_other _ _ _ _ (cS_ne i hi)⟩
  rw [← e0, install_slot _ cS_inj, hA', hO]

end Gen

/-! ## The machine -/

/-- The THR converter's slots: the two carrier slots, then the tuple's table. -/
def thrJ : List (Fin 6) := [0, 1, 2]

noncomputable def convM3 := MaskedReset.machine (C4Gates.convAll thrJ).toProg.compile (fun _ => true)

/-- The THR writer before its teardown: the front, the copy, the THR data stage, the converter over `thrJ`. -/
noncomputable def gtInner (D : PrimAsm.ThrData.ThrDataStage2) (Dv Cv : ℕ) :=
  Composition.machine (Composition.machine (Composition.machine
    (RecoveryFocus.machine (gl (Dv := Dv)) (gsFront Dv Cv)) (RecoveryFocus.machine (kS (Dv := Dv)) copyM))
    (RecoveryFocus.machine (dS (Dv := Dv)) D.M)) (RecoveryFocus.machine (cS (Dv := Dv)) convM3)

/-- **The THR gate-frame writer** (every head back at `0`). -/
noncomputable def gtM (D : PrimAsm.ThrData.ThrDataStage2) (Dv Cv : ℕ) :=
  MaskedReset.machine (gtInner D Dv Cv) (fun _ => true)

/-! ## The slots -/

section Slots
variable {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The THR converter's slot `j`**: the carriers' doubled atoms (`0, 1`), the tuple's occurrences (`2`). -/
def gtG (j : Fin 6) : List (NormalizedThresholdGate n) :=
  if j.val < 2 then (carriers.map FinalPass.Corner.maskGates).getD j.val []
  else if j.val = 2 then PrimT.ThrTab.tupleG Cs else []

/-- The slot's table width (`1` for a blank slot). -/
def gtH (j : Fin 6) : ℕ :=
  if j.val < 2 then (carriers.map fun X => max 1 (PrimT.tabH X)).getD j.val 1
  else if j.val = 2 then max 1 (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) else 1

/-- A bound for the three slots' widths. -/
def gtHs : ℕ := gtH Cs carriers 0 + gtH Cs carriers 1 + gtH Cs carriers 2

theorem thrJ_flatMap {β : Type} (f : Fin 6 → List β) : thrJ.flatMap f = f 0 ++ f 1 ++ f 2 := by
  simp [thrJ, List.append_assoc]

theorem tupleG_nil (h : a' = 0) : PrimT.ThrTab.tupleG Cs = [] := by
  subst h
  simp [PrimT.ThrTab.tupleG]

/-- **The THR pool is the three slots' concatenation.** -/
theorem thrPool_eq (P : Shared.StarParams) (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (hk : carriers.length ≤ 2) :
    PrimAsm.Records.thrPool P Cs carriers = thrJ.flatMap (gtG Cs carriers) := by
  unfold PrimAsm.Records.thrPool PrimAsm.Records.thrSlices
  rw [List.flatten_append, flat2 _ (by rw [List.length_map]; exact hk), thrJ_flatMap, PrimT.ThrTab.thrOccs_gates]
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil, List.append_assoc] <;> rfl

theorem gtG_car (j : Fin 6) (h : j.val < 2) (hk : j.val < carriers.length) :
    gtG Cs carriers j = FinalPass.Corner.maskGates (carriers.get ⟨j.val, hk⟩) := by
  unfold gtG
  rw [if_pos h, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]
  rfl

theorem gtH_car (j : Fin 6) (h : j.val < 2) (hk : j.val < carriers.length) :
    gtH Cs carriers j = max 1 (PrimT.tabH (carriers.get ⟨j.val, hk⟩)) := by
  unfold gtH
  rw [if_pos h, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hk), List.getElem_map]
  rfl

theorem gtG_carE (j : Fin 6) (h : j.val < 2) (hk : carriers.length ≤ j.val) : gtG Cs carriers j = [] := by
  unfold gtG
  rw [if_pos h, List.getD_eq_default _ _ (by rw [List.length_map]; exact hk)]

theorem gtH_carE (j : Fin 6) (h : j.val < 2) (hk : carriers.length ≤ j.val) : gtH Cs carriers j = 1 := by
  unfold gtH
  rw [if_pos h, List.getD_eq_default _ _ (by rw [List.length_map]; exact hk)]

theorem gtG_two : gtG Cs carriers 2 = PrimT.ThrTab.tupleG Cs := rfl

theorem gtH_two : gtH Cs carriers 2 = max 1 (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) := rfl

/-- **The THR data stage's tables are the converter's slots** (`tabS = sSym 0 3`; a blank slot's table is blank). -/
theorem slot_T3 (tabS : Fin (PrimAsm.Data.DS + 1)) (hD : tabS = PrimAsm.Data.sSym 0 3)
    (tout : Fin (PrimAsm.Data.DS + 2 + PrimAsm.Data.DR) → List Bool)
    (f1 : tout (sTape tabS) = (if a' = 0 then [] else
      FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)))
    (f2 : ∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (PrimAsm.Data.sCar k 3)) =
      FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
        (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩)))
    (f4 : ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (PrimAsm.Data.sCar k 3)) = []) (j : Fin 6)
    (hj : j ∈ thrJ) :
    tout (sTape (tabStream j)) = FinalPass.Corner.gatesW (gtH Cs carriers j) (gtG Cs carriers j) ∨
      (tout (sTape (tabStream j)) = [] ∧ gtG Cs carriers j = []) := by
  by_cases h : j.val < 2
  · have et : tabStream j = PrimAsm.Data.sCar ⟨j.val, h⟩ 3 := by unfold tabStream; rw [dif_pos h]
    rw [et]
    by_cases hk : j.val < carriers.length
    · left
      rw [f2 ⟨j.val, h⟩ hk, gtG_car Cs carriers j h hk, gtH_car Cs carriers j h hk,
        gatesW_max1 _ _ (mask_pos _)]
    · right
      exact ⟨f4 ⟨j.val, h⟩ (by show carriers.length ≤ j.val; omega), gtG_carE Cs carriers j h (by omega)⟩
  · have hj2 : j = 2 := by
      simp only [thrJ, List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl
      · exact absurd (show (0 : Fin 6).val < 2 by decide) h
      · exact absurd (show (1 : Fin 6).val < 2 by decide) h
      · rfl
    subst hj2
    have et : tabStream 2 = tabS := by rw [hD]; rfl
    rw [et, f1, gtG_two, gtH_two]
    by_cases h0 : a' = 0
    · right
      rw [if_pos h0]
      exact ⟨rfl, tupleG_nil Cs h0⟩
    · left
      rw [if_neg h0, gatesW_max1 _ _ (tabH_pos' _)]

/-- **The THR widths meet the converter's bounds.** -/
theorem slot_H3 (j : Fin 6) (hj : j ∈ thrJ) : 1 ≤ gtH Cs carriers j ∧ gtH Cs carriers j ≤ gtHs Cs carriers ∧
    ∀ g ∈ gtG Cs carriers j, C4Gates.GB (gtH Cs carriers j) g := by
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by
    simp only [thrJ, List.mem_cons, List.not_mem_nil, or_false] at hj
    exact hj
  have hle : gtH Cs carriers j ≤ gtHs Cs carriers := by
    unfold gtHs
    rcases hj3 with rfl | rfl | rfl <;> omega
  refine ⟨?_, hle, ?_⟩
  · rcases hj3 with rfl | rfl | rfl
    · by_cases hk : (0 : Fin 6).val < carriers.length
      · rw [gtH_car Cs carriers 0 (by decide) hk]; exact le_max_left _ _
      · rw [gtH_carE Cs carriers 0 (by decide) (by omega)]
    · by_cases hk : (1 : Fin 6).val < carriers.length
      · rw [gtH_car Cs carriers 1 (by decide) hk]; exact le_max_left _ _
      · rw [gtH_carE Cs carriers 1 (by decide) (by omega)]
    · rw [gtH_two]; exact le_max_left _ _
  · intro g hg
    rcases hj3 with rfl | rfl | rfl
    · by_cases hk : (0 : Fin 6).val < carriers.length
      · rw [gtG_car Cs carriers 0 (by decide) hk] at hg
        rw [gtH_car Cs carriers 0 (by decide) hk, max_eq_right (mask_pos _ (List.ne_nil_of_mem hg))]
        exact mask_GB _ g hg
      · rw [gtG_carE Cs carriers 0 (by decide) (by omega)] at hg
        exact absurd hg List.not_mem_nil
    · by_cases hk : (1 : Fin 6).val < carriers.length
      · rw [gtG_car Cs carriers 1 (by decide) hk] at hg
        rw [gtH_car Cs carriers 1 (by decide) hk, max_eq_right (mask_pos _ (List.ne_nil_of_mem hg))]
        exact mask_GB _ g hg
      · rw [gtG_carE Cs carriers 1 (by decide) (by omega)] at hg
        exact absurd hg List.not_mem_nil
    · rw [gtG_two] at hg
      rw [gtH_two, max_eq_right (tabH_pos' _ (List.ne_nil_of_mem hg))]
      exact C4Gates.GB_tabH _ g hg

end Slots

/-! ## The run -/

/-- **The THR gate-frame writer's run**: from `frame w` (`w` the THR request word's shape), the output port holds
C3a's gate field of the THR call's pool, the request kept, within `2·gsCost + 2` steps. -/
theorem gt_run (D : PrimAsm.ThrData.ThrDataStage2) (hD : D.tabS = PrimAsm.Data.sSym 0 3) (Dv Cv Bud : ℕ)
    (P : Shared.StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (tl : List Bool) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (W : ℕ) (hW : UnaryCalc.value Dv Cv P.n = W)
    (hL : ∀ i, (Cs i).descriptionBits ≤ W) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ W)
    (h2 : 2 ≤ P.n + W)
    (hcN : natBitLength P.n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ PrimAsm.ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + W ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + P.n + W ≤ 2 * W + 2)
    (hcu : 2 * (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2)
    (hB : 2 * gsCost (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl)
      P.n Dv Cv (D.cost a' Cs carriers W W) (PrimAsm.Records.thrPool P Cs carriers).length
      (gtHs Cs carriers) + 2 ≤ Bud) :
    PrimAsm.WriterIfaceJ.WriterRun (gtM D Dv Cv) Bud (gsIn Dv) (gsOut Dv)
      (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl)
      (C4Geo.gateField (PrimAsm.Records.thrPool P Cs carriers)) := by
  obtain ⟨w, hwd⟩ : ∃ x, x = PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
      (carriers.map Stars.Carrier.code) tl := ⟨_, rfl⟩
  rw [← hwd] at hB ⊢
  have hsfx : w = RepairRepresentation.natWord P.n ++ ([true] ++
      RepairRepresentation.natWord (PrimAsm.ReqBridge.thrCodes Cs).length ++
      (PrimAsm.ReqBridge.thrCodes Cs).flatMap RepairRepresentation.natWord ++
      RepairRepresentation.natListWord (carriers.map Stars.Carrier.code) ++ tl) := by
    rw [hwd]
    unfold PrimAsm.Data.reqW
    simp only [List.append_assoc]
  have hG : 16 ≤ GLt Dv := by show 16 ≤ 78 + (14 + (14 + 2 * Dv)); omega
  have hDT : DT = 9902 := rfl
  -- 1: the front
  obtain ⟨E1, s1, e1in, e1nt, e1ct, e1z⟩ := front_stage (Dv := Dv) Cv P.n w _ hsfx
  rw [hW] at e1ct
  -- 2: the copy
  obtain ⟨K', s2, e2lt, e2ns, e2ct, e2nt⟩ := copy_step E1 P.n W e1ct e1nt
    (e1z _ (by rw [dReg_val]; omega)) (e1z _ (by rw [cReg_val]; omega)) (fun c => e1z _ (by rw [kReg_val]; omega))
  have e2in : install kS E1 K' (gl (ws gIN)) = frame w := by
    rw [install_other _ _ _ _ (kS_ne _ (by rw [gl_val, ws_IN]; omega) (by rw [gl_val, ws_IN]; omega)
      (by rw [gl_val, ws_IN]; omega) (Or.inl (by rw [gl_val, ws_IN]; omega)) (by rw [gl_val, ws_IN]; omega)), e1in]
  have e2z : ∀ d : Fin DT, d.val ≠ 3 → install kS E1 K' (dReg d) = [] := by
    intro d hd
    have := d.isLt
    rw [install_other _ _ _ _ (kS_ne _ (by rw [dReg_val]; omega) (by rw [dReg_val]; omega)
      (by rw [dReg_val]; omega) (Or.inl (by rw [dReg_val]; omega)) (by rw [dReg_val]; omega)),
      e1z _ (by rw [dReg_val]; omega)]
  have e2c : ∀ x : Fin 34, x.val ≠ 11 → install kS E1 K' (cReg x) = [] := by
    intro x hx
    rw [install_other _ _ _ _ (kS_ne _ (by rw [cReg_val]; omega) (by rw [cReg_val]; omega)
      (by rw [cReg_val]; omega) (Or.inr (by rw [cReg_val]; omega)) (by rw [cReg_val]; omega)),
      e1z _ (by rw [cReg_val]; omega)]
  -- 3: the THR data stage
  obtain ⟨tout, m, sD, _, t_in, f1, f2, f4⟩ := D.run Cs carriers tl W W ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu
  rw [← hwd] at sD t_in
  have s3 := data_stageM D.M (install kS E1 K') w P.n W _ m tout sD e2in e2nt e2lt e2ct e2z
  obtain ⟨a1, a2, a3⟩ := data_after (install kS E1 K') (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))
  -- 4: the converter over the three slots
  obtain ⟨E4, s4, e4o, e4k⟩ := conv_stageJ thrJ (by decide)
    (install dS (install kS E1 K') (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))) P.n
    (gtHs Cs carriers) (gtG Cs carriers) (gtH Cs carriers)
    (by rw [a3, e2ns]) (fun x hx => by rw [a3]; exact e2c x hx)
    (fun j hj => by rw [a2, addCases_dPos]; exact slot_T3 Cs carriers D.tabS hD tout f1 f2 f4 j hj)
    (fun j hj => slot_H3 Cs carriers j hj)
  rw [← thrPool_eq P Cs carriers hk] at s4 e4o
  -- the whole writer
  have si := ((s1.seq s2).seq s3).seq s4
  obtain ⟨mm, sm⟩ := ListMachine.Row.maskBlank si (fun _ => true) (fun _ _ => rfl) 0
  have eh1 : (Fin.addCases (fun _ => 0) (fun _ : Fin 1 => 0) : Fin (GT Dv + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have eh3 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else (fun _ => 0 : Fin (GT Dv) → ℕ) i)
      (fun _ : Fin 1 => 0) : Fin (GT Dv + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hstep := (sm.congr_in eh1 (gsA0_in w)).congr eh3 rfl
  unfold gsCost at hB
  rw [hW] at hB
  refine writerRun_of_step hstep ?_ ?_ (gsIn_ne_out Dv) (by omega)
  · show Fin.addCases E4 (fun _ : Fin 1 => List.replicate mm false) (Fin.castAdd 1 (gl (ws gIN))) = frame w
    rw [Fin.addCases_left, e4k _ (by rw [gl_val, ws_IN]; omega), a1, addCases_dPos, t_in]
  · show Fin.addCases E4 (fun _ : Fin 1 => List.replicate mm false) (Fin.castAdd 1 (cReg 0)) =
      C4Geo.gateField (PrimAsm.Records.thrPool P Cs carriers)
    rw [Fin.addCases_left, e4o]

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym
