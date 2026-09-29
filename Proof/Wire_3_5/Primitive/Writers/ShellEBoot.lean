import Proof.Wire_3_5.Primitive.Writers.ShellT2
import Proof.Wire_3_5.Primitive.ThresholdWriter.ShellE

/-! # The ShellE: the THR writer shell over `ThrDataStage2`, part 1: the boot

The boot (`ShellTBoot`: `st8T`, `pre_stepT`, `x0_stepT`, `bootX_stepG`) runs over a `ThrDataStage` and `ThrDataOK`,
both with `1 ≤ a'`. The relaxed types (`PrimThrW.ShellE`) cover the empty tuple: the stage is a
`ThrDataStage2` (the M30), used through `ShellE.toV1` (the same machine and cost), and the size hypotheses are
`ThrDataOK2`. The boot's proofs are the with `S.run` of the v2 stage (no `1 ≤ a'`); the machines are the at
`toV1 S` (`M8T`, `preMT`, `MX0T`, `bootXMG`), so one machine family serves both.

* `st8E`, **`pre_stepE`**, `x0_stepE`, **`bootX_stepE`** (any `DimOK` stage, every `a' ≤ 4`).

Paper quantity of the main type: the THR call's slice lengths `ThrData.thrCounts` on the writer's data tape, ending
in `0` at the empty tuple (lem:primitive P3:3068: tuple arity at most four). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.PrimAsm.ShellT
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.SymLayout
open NearCubicWires.WireExponent3_5.PrimAsm.CellLoop NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5 NearCubicWires.WireExponent3_5.ListMachine
open NearCubicWires.WireExponent3_5.PrimAsm.ShellD NearCubicWires.WireExponent3_5.PrimAsm.ShellX
open NearCubicWires.SupplierPipeline
open NearCubicWires.WireExponent3_5.PrimAsm.Shell (install_eq dockH_eq)

section Data
variable {x D D1 D2 : ℕ}

theorem st8E (S : ThrData.ThrDataStage2) {n : ℕ} (a' : ℕ)
    (Cs : Fin a' → SupplierPipeline.NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (tl : List Bool) (V : ℕ) (H : Fin (STd x D D1 D2) → ℕ)
    (Bin : Fin (STd x D D1 D2) → List Bool) (hH : ∀ j, H (dataSlots x D D1 D2 j) = 0)
    (hIN : Bin (cs 0) = RepairOrdinary.frame (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl))
    (hNT : Bin (e1T (UnaryCalc.inputTape D1)) = List.replicate n true)
    (hLT : Bin (e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2))) = List.replicate V true)
    (hOUT : Bin dT = []) (hCT : Bin (e3T ctPos) = List.replicate V true)
    (hrest : ∀ j, j ≠ inPos → j ≠ ntPos → j ≠ ltPos → j ≠ outPos → j ≠ ctPos → Bin (e3T j) = [])
    (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ V) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ V)
    (h2 : 2 ≤ n + V)
    (hcN : natBitLength n + 1 ≤ 2 * V + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * V + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * V + 2)
    (hcx : ∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + V ≤ 2 * V + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + n + V ≤ 2 * V + 2)
    (hcu : 2 * (Data.unaryList (ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * V + 2) :
    ∃ (tout : Fin (Data.DS + 2 + Data.DR) → List Bool) (m : ℕ),
      Step (PrimThrW.Shell.M8T (PrimThrW.ShellE.toV1 S) x D D1 D2) (S.cost a' Cs carriers V V) H Bin H
        (install (dataSlots x D D1 D2) Bin (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false))) ∧
      tout (sTape Data.sOUT) = Data.dataWord (ThrData.thrCounts Cs carriers) ∧
      tout (sTape Data.sIN) =
        RepairOrdinary.frame (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) := by
  obtain ⟨tout, m, hs, hO, hI, _, _⟩ := S.run Cs carriers tl V V ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu
  have hne_in : ∀ s, s ≠ Data.sIN → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ inPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_nt : ∀ s, s ≠ Data.sNT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ ntPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_lt : ∀ s, s ≠ Data.sLT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ ltPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_out : ∀ s, s ≠ Data.sOUT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ outPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have hne_ct : ∀ s, s ≠ Data.sCT → (Fin.castAdd 1 (sTape (nr := Data.DR) s) : Fin E3) ≠ ctPos :=
    fun s hs e => hs ((pos_eq _ _).mp e)
  have gen : ∀ j : Fin E3, j ≠ inPos → j ≠ ntPos → j ≠ ltPos → j ≠ outPos → dataSlots x D D1 D2 j = e3T j := by
    intro j a1 a2 a3 a4
    simp [dataSlots, a1, a2, a3, a4]
  have d := Rec.dockRun hs (dataSlots x D D1 D2) dataSlots_inj H Bin (fun j => hH j) (by
    intro j
    refine Fin.addCases (fun t => ?_) (fun u => ?_) j
    · simp only [Fin.addCases_left]
      rcases tape_cases t with ⟨s, rfl⟩ | rfl | ⟨r, rfl⟩
      · rw [Data.rawIn_s]
        by_cases s1 : s = Data.sIN
        · subst s1
          simp only [dataSlots, inPos, if_true, if_pos rfl]
          exact hIN
        · by_cases s2 : s = Data.sNT
          · subst s2
            simp only [dataSlots, if_neg (hne_in _ s1), ntPos, if_true]
            simp [Data.sNT, Data.sIN]
            exact hNT
          · by_cases s3 : s = Data.sLT
            · subst s3
              simp only [dataSlots, if_neg (hne_in _ s1), if_neg (hne_nt _ s2), ltPos, if_true]
              simp [Data.sLT, Data.sIN, Data.sNT]
              exact hLT
            · by_cases s4 : s = Data.sOUT
              · subst s4
                simp only [dataSlots, if_neg (hne_in _ s1), if_neg (hne_nt _ s2), if_neg (hne_lt _ s3), outPos,
                  if_true]
                simp [Data.sOUT, Data.sIN, Data.sNT, Data.sLT, Data.sCT]
                exact hOUT
              · rw [gen _ (hne_in _ s1) (hne_nt _ s2) (hne_lt _ s3) (hne_out _ s4)]
                by_cases s5 : s = Data.sCT
                · subst s5
                  simp [Data.sCT, Data.sIN, Data.sNT, Data.sLT]
                  exact hCT
                · rw [hrest _ (hne_in _ s1) (hne_nt _ s2) (hne_lt _ s3) (hne_out _ s4) (hne_ct _ s5)]
                  simp [s1, s2, s3, s5]
      · have c1 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ inPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c2 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ ntPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c3 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ ltPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c4 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ outPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        have c5 : (Fin.castAdd 1 (cTape (ns := Data.DS) (nr := Data.DR)) : Fin E3) ≠ ctPos :=
          fun e => sTape_ne_c _ (Fin.castAdd_injective _ _ e).symm
        rw [gen _ c1 c2 c3 c4, hrest _ c1 c2 c3 c4 c5, Data.rawIn_c]
      · have c1 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ inPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c2 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ ntPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c3 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ ltPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c4 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ outPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        have c5 : (Fin.castAdd 1 (rTape (ns := Data.DS) r) : Fin E3) ≠ ctPos :=
          fun e => sTape_ne_r _ _ (Fin.castAdd_injective _ _ e).symm
        rw [gen _ c1 c2 c3 c4, hrest _ c1 c2 c3 c4 c5, Data.rawIn_r]
    · have lne : ∀ q : Fin (Data.DS + 2 + Data.DR), (Fin.natAdd (Data.DS + 2 + Data.DR) u : Fin E3) ≠ Fin.castAdd 1 q :=
        fun q e => by
          have := congrArg Fin.val e
          simp at this
          have := q.isLt
          omega
      rw [gen _ (lne _) (lne _) (lne _) (lne _), hrest _ (lne _) (lne _) (lne _) (lne _) (lne _)]
      simp)
  exact ⟨tout, m, d.congr (dockH_eq _ dataSlots_inj _ _ _ (fun j => hH j) (fun _ _ => rfl)) rfl, hO, hI⟩

end Data

section Pre
variable {x D D1 D2 : ℕ}

/-- **The boot and the data phase as one run**: from the writer's entry bank on the call's request word, the loop's
entry data (request kept, `OUT = [false]`, unit counter blank, workspace `Scrub.calcIn D n`, log and driver blank,
counter `word b`) and the DATA TAPE `Data.dataWord (Data.symCounts a' Cs carriers)`; the cell's scratch within the
boot's cost. -/
theorem pre_stepE (S : ThrData.ThrDataStage2) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (C1 C2 : ℕ)
    (hw : w = Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value D2 C2 n)) :
    ∃ B8 : Fin (STd x D D1 D2) → List Bool,
      Step (PrimThrW.Shell.preMT (PrimThrW.ShellE.toV1 S) x D D1 D2 C1 C2) (preCost w n D1 C1 D2 C2
          (S.cost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)))
        (fun _ => 0) (B0 w) (hK x D D1 D2) B8 ∧
      B8 (cs 0) = frame w ∧ B8 (cs 1) = [false] ∧ B8 (cs 2) = [] ∧ (∀ j, B8 (wT j) = Scrub.calcIn D n j) ∧
      B8 lgT = [] ∧ B8 drT = [] ∧
      B8 kT = RepairSource.VerifierDecoding.CompareMachine.word (UnaryCalc.value D1 C1 n) ∧
      B8 dT = Data.dataWord (ThrData.thrCounts Cs carriers) ∧
      (∀ c, kept x c = false → (B8 (cT c)).length ≤ bootCost w n D1 C1) := by
  have hT : 674 ≤ TT x := by unfold TT LNS LNR; omega
  obtain ⟨B5, sb, h0, h1, h2, hwk, hl, hd, hkk, hdt, hin, hhi⟩ :=
    boot_step (x := x) (D := D) (D1 := D1) (D2 := D2) w _ n C1 (hw.trans (reqW_natWord _ _ _ _ _))
  set V := UnaryCalc.value D2 C2 n with hV
  -- stage 6: `1^V`
  obtain ⟨out6, s6, o6i, o6o⟩ := st6 (x := x) (D := D) (D1 := D1) (D2 := D2) C2 n (hK x D D1 D2) B5
    (fun k => hK_low _ (p2Slots_val_ge k)) hin
    (fun k _ => hhi _ (by rw [e2T_val]; omega))
  set B6 := install (p2Slots x D D1 D2) B5 out6 with hB6
  have b6other : ∀ i, (∀ k, p2Slots x D D1 D2 k ≠ i) → B6 i = B5 i := fun i hi => install_other _ _ _ _ hi
  have b6o : B6 (e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2))) = List.replicate V true := by
    have e := install_slot (p2Slots x D D1 D2) p2Slots_inj B5 out6 (UnaryCalc.outputTape D2)
    rw [p2_out] at e
    rw [hB6, e, o6o]
  have b6i : B6 (e1T (UnaryCalc.inputTape D1)) = List.replicate n true := by
    have e := install_slot (p2Slots x D D1 D2) p2Slots_inj B5 out6 (UnaryCalc.inputTape D2)
    rw [p2_in] at e
    rw [hB6, e, o6i]
  -- stage 7: a second `1^V`
  have s7 := st7 (x := x) (D := D) (D1 := D1) (D2 := D2) V (hK x D D1 D2) B6
    (fun k => hK_low _ (by have := cpSlots2_val_ge (x := x) (D := D) (D1 := D1) (D2 := D2) k; omega)) b6o
    (by rw [b6other _ (fun k => p2Slots_ne_e2n k 0)]; exact hhi _ (by rw [e2T_val]; omega))
    (by rw [b6other _ (fun k => p2Slots_ne_e3T k ctPos)]; exact hhi _ (by rw [e3T_val]; omega))
    (by rw [b6other _ (fun k => p2Slots_ne_e2n k 1)]; exact hhi _ (by rw [e2T_val]; omega))
  set B7 := install (cpSlots2 x D D1 D2) B6
    ![List.replicate V true, [], List.replicate V true, List.replicate (V + 2) false] with hB7
  have b7other : ∀ i, (∀ m, cpSlots2 x D D1 D2 m ≠ i) → B7 i = B6 i := fun i hi => install_other _ _ _ _ hi
  have low7 : ∀ i : Fin (STd x D D1 D2), i.val < TT x + 1 + Scrub.wk D + 3 → B7 i = B5 i := by
    intro i hi
    rw [b7other _ (fun m => cpSlots2_ne_low m i (by omega)), b6other _ (fun k => p2Slots_ne_low k i hi)]
  have hc0 : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 0).val = 0 := rfl
  have b7cs0 : B7 (cs 0) = frame (Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) := by
    rw [low7 _ (by rw [hc0]; omega), h0, hw]
  have b7nt : B7 (e1T (UnaryCalc.inputTape D1)) = List.replicate n true := by
    rw [b7other _ (fun m => cpSlots2_ne_low m _ (e1T_lt _)), b6i]
  have b7lt : B7 (e2T (Fin.castAdd 2 (UnaryCalc.outputTape D2))) = List.replicate V true := by
    have e := install_slot (cpSlots2 x D D1 D2) cpSlots2_inj B6
      ![List.replicate V true, [], List.replicate V true, List.replicate (V + 2) false] 0
    rw [hB7]
    exact e
  have b7out : B7 dT = [] := by
    rw [low7 _ (by rw [dT_val]; omega), hdt]
  have b7ct : B7 (e3T ctPos) = List.replicate V true := by
    have e := install_slot (cpSlots2 x D D1 D2) cpSlots2_inj B6
      ![List.replicate V true, [], List.replicate V true, List.replicate (V + 2) false] 2
    rw [hB7]
    exact e
  have b7rest : ∀ j, j ≠ inPos → j ≠ ntPos → j ≠ ltPos → j ≠ outPos → j ≠ ctPos → B7 (e3T j) = [] := by
    intro j _ _ _ _ hj
    rw [b7other _ (fun m => cpSlots2_ne_e3T m j hj), b6other _ (fun k => p2Slots_ne_e3T k j)]
    exact hhi _ (by rw [e3T_val]; omega)
  -- stage 8: the data stage
  obtain ⟨tout, m8, s8, t8o, t8i⟩ := st8E S (x := x) (D := D) (D1 := D1) (D2 := D2) a' Cs carriers tl V (hK x D D1 D2) B7
    (fun j => by unfold hK; rw [if_neg (dataSlots_ne_kT j)]) b7cs0 b7nt b7lt b7out b7ct b7rest
    hD.ha hD.hk hD.hL hD.hLX hD.h2 hD.hcN hD.hcA hD.hcK hD.hcx hD.hcy hD.hcu
  set B8 := install (dataSlots x D D1 D2) B7 (Fin.addCases tout (fun _ : Fin 1 => List.replicate m8 false)) with hB8
  have low8 : ∀ i : Fin (STd x D D1 D2), i.val < TT x + 1 + Scrub.wk D + 3 → i ≠ cs 0 → i ≠ dT → B8 i = B5 i := by
    intro i hi hi0 hid
    rw [hB8, install_other _ _ _ _ (fun j => dataSlots_ne_low j i hi hi0 hid), low7 i hi]
  have ncs0 : ∀ i : Fin (STd x D D1 D2), 0 < i.val → i ≠ cs 0 := fun i h e => by
    rw [e, hc0] at h
    omega
  have ndT : ∀ i : Fin (STd x D D1 D2), i.val ≠ TT x → i ≠ dT := fun i h e => by
    rw [e, dT_val] at h
    exact h rfl
  refine ⟨B8, (((sb.seq s6).seq s7).seq s8).enlarge (by unfold preCost; omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e := install_slot (dataSlots x D D1 D2) dataSlots_inj B7 (Fin.addCases tout (fun _ : Fin 1 => List.replicate m8 false))
      inPos
    rw [data_in] at e
    rw [hB8, e, hw]
    exact t8i
  · have h1v : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 1).val = 2 := rfl
    rw [low8 _ (by rw [h1v]; omega) (ncs0 _ (by rw [h1v]; omega)) (ndT _ (by rw [h1v]; omega)), h1]
  · have h2v : (cs (x := x) (D := D) (D1 := D1) (D2 := D2) 2).val = 3 := rfl
    rw [low8 _ (by rw [h2v]; omega) (ncs0 _ (by rw [h2v]; omega)) (ndT _ (by rw [h2v]; omega)), h2]
  · intro j
    have := j.isLt
    rw [low8 _ (by rw [wT_val]; omega) (ncs0 _ (by rw [wT_val]; omega)) (ndT _ (by rw [wT_val]; omega)), hwk j]
  · rw [low8 _ (by rw [lgT_val]; omega) (ncs0 _ (by rw [lgT_val]; omega)) (ndT _ (by rw [lgT_val]; omega)), hl]
  · rw [low8 _ (by rw [drT_val]; omega) (ncs0 _ (by rw [drT_val]; omega)) (ndT _ (by rw [drT_val]; omega)), hd]
  · rw [low8 _ (by rw [kT_val]; omega) (ncs0 _ (by rw [kT_val]; omega)) (ndT _ (by rw [kT_val]; omega)), hkk]
  · have e := install_slot (dataSlots x D D1 D2) dataSlots_inj B7 (Fin.addCases tout (fun _ : Fin 1 => List.replicate m8 false))
      outPos
    rw [data_out] at e
    rw [hB8, e]
    exact t8o
  · intro c hc
    have hne : cT (x := x) (D := D) (D1 := D1) (D2 := D2) c ≠ cs 0 := by
      intro e
      have e' : c = sTape (sk x 0) := cT_inj e
      subst e'
      simp [kept] at hc
    have hlt := c.isLt
    rw [low8 _ (by rw [cT_val]; omega) hne (ndT _ (by rw [cT_val]; omega))]
    have := Shell.Step.len sb (cT c) 0 (le_refl _) (by simp [B0, hne])
    omega

end Pre

section Boot
variable {x D D2 Dv DL : ℕ}

theorem x0_stepE (S : ThrData.ThrDataStage2) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (C2 : ℕ)
    (hw : w = Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value D2 C2 n)) :
    ∃ B8 : Fin (SD x D D2) → List Bool,
      Step (PrimThrW.Shell.MX0T (PrimThrW.ShellE.toV1 S) x D D2 Dv DL C2) (preCost w n 0 0 D2 C2
          (S.cost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)))
        (fun _ => 0) (A0 w) HI (install pX (A0 w) B8) ∧
      B8 (cs 0) = frame w ∧ B8 (cs 1) = [false] ∧ B8 (cs 2) = [] ∧ (∀ j, B8 (wT j) = Scrub.calcIn D n j) ∧
      B8 dT = Data.dataWord (ThrData.thrCounts Cs carriers) ∧
      (∀ c, kept x c = false → (B8 (cT c)).length ≤ bootCost w n 0 0) := by
  obtain ⟨B8, sp, h0, h1, h2, hwk, -, -, -, hdt, hs⟩ :=
    pre_stepE S (x := x) (D := D) (D1 := 0) (D2 := D2) Cs carriers tl w 0 C2 hw hD
  have d := Rec.dockRun sp (pX (Dv := Dv) (DL := DL)) (pX_inj (Dv := Dv) (DL := DL)) (fun _ => 0) (A0 w)
    (fun _ => rfl) (by
    intro j
    by_cases hj : j = cs 0
    · subst hj
      rw [pX_lo _ cs0_lt]
      simp [A0, B0]
    · have hne : pX (Dv := Dv) (DL := DL) j ≠ lo (cs 0) := by
        intro e
        rw [← pX_lo (Dv := Dv) (DL := DL) _ cs0_lt] at e
        exact hj (pX_inj e)
      simp only [A0, B0, if_neg hne, if_neg hj])
  have hk := kT_ge (x := x) (D := D) (D2 := D2)
  refine ⟨B8, d.congr ?_ rfl, h0, h1, h2, hwk, hdt, hs⟩
  refine Shell.dockH_eq _ pX_inj _ _ _ ?_ ?_
  · intro j
    by_cases hj : j = kT
    · subst hj
      rw [pX_im _ hk, hK_kT]
      simp [HI]
    · have hne : pX (Dv := Dv) (DL := DL) j ≠ im kT := by
        intro e
        rw [← pX_im (Dv := Dv) (DL := DL) _ hk] at e
        exact hj (pX_inj e)
      rw [hK_ne _ hj]
      simp [HI, hne]
  · intro i hi
    have hne : i ≠ im kT := by
      intro e
      rw [e, ← pX_im (Dv := Dv) (DL := DL) _ hk] at hi
      exact hi _ rfl
    simp [HI, hne]

theorem bootX_stepE (S : ThrData.ThrDataStage2) {s2 : ℕ} (M2 : Machine NUn s2) (c2 m : ℕ) {n a' : ℕ}
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))
    (tl w : List Bool) (C2 Cv CL : ℕ)
    (hw : w = Data.reqW n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl)
    (hD : PrimThrW.ShellE.ThrDataOK2 Cs carriers (UnaryCalc.value D2 C2 n))
    (hx2 : DimOK x D D2 Dv DL M2 c2 m w (UnaryCalc.value Dv Cv n)) :
    ∃ Bf : Fin (STx x D D2 Dv DL) → List Bool,
      Step (bootXMG (PrimThrW.ShellE.toV1 S) x D D2 Dv DL C2 Cv CL M2) (bootXCostG w n D2 C2
          (S.cost a' Cs carriers (UnaryCalc.value D2 C2 n) (UnaryCalc.value D2 C2 n)) Dv Cv c2 m DL CL)
        (fun _ => 0) (A0 w) (HF x D D2 Dv DL) Bf ∧
      Bf (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0)) = frame w ∧
      Bf (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)) = [false] ∧
      Bf (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 2)) = [] ∧
      (∀ c, kept x c = false → (Bf (lo (cT (D := D) (D1 := 0) (D2 := D2) c))).length ≤ bootCost w n 0 0) ∧
      (∀ j, Bf (lo (wT (x := x) (D1 := 0) (D2 := D2) j)) = Scrub.calcIn D (2 ^ m) j) ∧
      Bf (lo (lgT (x := x) (D := D) (D1 := 0) (D2 := D2))) = [] ∧
      Bf (lo (drT (x := x) (D := D) (D1 := 0) (D2 := D2))) = [] ∧
      Bf (TK x D D2 Dv DL) = RepairSource.VerifierDecoding.CompareMachine.word
        (UnaryCalc.value DL CL (2 ^ m)) ∧
      Bf (lo (dT (x := x) (D := D) (D1 := 0) (D2 := D2))) = Data.dataWord (ThrData.thrCounts Cs carriers) := by
  have hsd := SD_ge (x := x) (D := D) (D2 := D2)
  have hT := TT_lt_SD (x := x) (D := D) (D2 := D2)
  have hTT : 674 ≤ TT x := by unfold TT LNS LNR; omega
  have hN : NUn = 38 := rfl
  have hwk1 : 1 ≤ Scrub.wk D := by rw [Scrub.wk_eq]; omega
  obtain ⟨W, hWd⟩ : ∃ W, UnaryCalc.value Dv Cv n = W := ⟨_, rfl⟩
  rw [hWd] at hx2
  obtain ⟨b, hb⟩ : ∃ b, UnaryCalc.value DL CL (2 ^ m) = b := ⟨_, rfl⟩
  rw [hb]
  -- 0
  obtain ⟨B8, s0, e0, e1, e2, ewk, edt, escr⟩ := x0_stepE S (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    Cs carriers tl w C2 hw hD
  obtain ⟨Bx0, hBx0⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (pX (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) (A0 w) B8 :=
    ⟨_, rfl⟩
  rw [← hBx0] at s0
  have b0lo : ∀ i : Fin (SD x D D2), i.val < TT x + 1 → Bx0 (lo i) = B8 i := by
    intro i hi
    rw [hBx0, ← pX_lo (Dv := Dv) (DL := DL) i hi]
    exact install_slot _ pX_inj _ _ i
  have b0hi : ∀ i : Fin (STx x D D2 Dv DL), SD x D D2 + SD x D D2 ≤ i.val → Bx0 i = [] := by
    intro i hi
    rw [hBx0, inst_keep _ _ _ _ (fun j => by
      unfold pX; split_ifs
      · have := lo_lt (Dv := Dv) (DL := DL) j; omega
      · have := im_lt (Dv := Dv) (DL := DL) j; omega)]
    have hne : i ≠ lo (cs 0) := by
      intro e; have := lo_lt (Dv := Dv) (DL := DL) (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0); rw [← e] at this; omega
    simp [A0, hne]
  have b0lo_ge : ∀ i : Fin (SD x D D2), TT x + 1 ≤ i.val → Bx0 (lo i) = [] := by
    intro i hi
    rw [hBx0, inst_keep _ _ _ _ (fun j => by
      unfold pX; split_ifs with hj
      · simp only [lo_val, lo_val]; omega
      · have := im_ge (Dv := Dv) (DL := DL) j; have := i.isLt; simp only [lo_val]; omega)]
    have hne : lo (Dv := Dv) (DL := DL) i ≠ lo (cs 0) := by
      intro e; have := congrArg Fin.val e; rw [lo_val, lo_val] at this
      have h0 : (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0).val = 0 := rfl
      omega
    simp [A0, hne]
  have b0im : ∀ i : Fin (SD x D D2), TT x + 1 ≤ i.val → Bx0 (im i) = B8 i := by
    intro i hi
    rw [hBx0, ← pX_im (Dv := Dv) (DL := DL) i hi]
    exact install_slot _ pX_inj _ _ i
  -- 1
  obtain ⟨out1, s1, o1⟩ := x1_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) Cv n Bx0
    (by
      show Bx0 (im (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)))) = _
      rw [b0im (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D))) (by rw [wT_val]; exact Nat.le_add_right _ _), ewk]
      simp only [Scrub.calcIn, Fin.addCases_left]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape])
    (fun k => b0hi _ (by simp only [e5_val]; omega))
  rw [hWd] at o1
  obtain ⟨Bx1, hBx1⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (q1 x D D2 Dv DL) Bx0 out1 := ⟨_, rfl⟩
  rw [← hBx1] at s1
  have k1 : ∀ i : Fin (STx x D D2 Dv DL), i.val < SD x D D2 → Bx1 i = Bx0 i := by
    intro i hi
    rw [hBx1, inst_keep _ _ _ _ (fun j => by have := q1_val_ge (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j; omega)]
  have k1' : ∀ i : Fin (STx x D D2 Dv DL), SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv ≤ i.val → Bx1 i = Bx0 i := by
    intro i hi
    rw [hBx1, inst_keep _ _ _ _ (fun j => by
      unfold q1; split_ifs
      · simp only [TI_val]; omega
      · rw [e5_val]; have := j.isLt; omega)]
  have o1' : Bx1 (TW x D D2 Dv DL) = List.replicate W true := by
    have hq : q1 x D D2 Dv DL (UnaryCalc.outputTape Dv) = TW x D D2 Dv DL := by
      unfold q1; rw [if_neg]; rfl
      intro e; have := congrArg Fin.val e; rw [outTape_val, inTape_val] at this; omega
    rw [hBx1, ← hq, install_slot _ q1_inj]
    exact o1
  -- 2
  obtain ⟨tout2, s2, o2, i2⟩ := hx2 Bx1
    (by rw [k1 (T0 x D D2 Dv DL) (by simp only [T0_val]; omega)]; show Bx0 (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0)) = _; rw [b0lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 0) cs0_lt, e0]) o1'
    (fun k => by
      rw [k1' (nu (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [nu_val]; omega)]
      exact b0hi _ (by simp only [nu_val]; omega))
  obtain ⟨Bx2, hBx2⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (q2 x D D2 Dv DL) Bx1 tout2 := ⟨_, rfl⟩
  rw [← hBx2] at s2
  have k2 : ∀ i : Fin (STx x D D2 Dv DL), i.val ≠ 0 → i.val < SD x D D2 + SD x D D2 → Bx2 i = Bx1 i := by
    intro i h0 hi
    rw [hBx2, inst_keep _ _ _ _ (fun j => by
      rcases q2_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with e | e <;> omega)]
  have k2' : ∀ i : Fin (STx x D D2 Dv DL), SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv + NUn ≤ i.val →
      Bx2 i = Bx1 i := by
    intro i hi
    rw [hBx2, inst_keep _ _ _ _ (fun j => by
      rcases q2_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨-, -, e⟩ <;>
        rw [e]
      · simp only [T0_val]; omega
      · rw [TW_val]; have := outTape_lt Dv; omega
      · rw [nu_val]; have := j.isLt; omega)]
  have o2' : Bx2 (TS x D D2 Dv DL) = NumsX.srcWord m := by
    have hq : q2 x D D2 Dv DL oN = TS x D D2 Dv DL := by
      unfold q2; rw [if_neg (by decide), if_neg (by decide)]; rfl
    rw [hBx2, ← hq, install_slot _ q2_inj]
    exact o2
  have i2' : Bx2 (T0 x D D2 Dv DL) = frame w := by
    have hq : q2 x D D2 Dv DL iN = T0 x D D2 Dv DL := by unfold q2; rw [if_pos rfl]
    rw [hBx2, ← hq, install_slot _ q2_inj]
    exact i2
  -- 3
  obtain ⟨out3, s3, o8, o9⟩ := x3_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) m Bx2 o2'
    (by
      have tc1 : (TC x D D2 Dv DL).val ≠ 0 := by rw [TC_val]; omega
      have tc2 : (TC x D D2 Dv DL).val < SD x D D2 + SD x D D2 := lt_of_lt_of_le hT (Nat.le_add_right _ _)
      have tc3 : (TC x D D2 Dv DL).val < SD x D D2 := hT
      rw [k2 (TC x D D2 Dv DL) tc1 tc2, k1 (TC x D D2 Dv DL) tc3]
      show Bx0 (lo (wT (x := x) (D1 := 0) (D2 := D2) (Fin.castAdd 1 (UnaryCalc.inputTape D)))) = []
      exact b0lo_ge _ (by rw [wT_val]; exact Nat.le_add_right _ _))
    (by
      rw [k2' (TE x D D2 Dv DL) (by simp only [TE_val]; omega), k1' (TE x D D2 Dv DL) (by simp only [TE_val]; omega)]
      exact b0hi _ (by simp only [TE_val]; omega))
    (fun k => by
      rw [k2' (ca (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [ca_val]; omega), k1' (ca (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [ca_val]; omega)]
      exact b0hi _ (by simp only [ca_val]; omega))
  obtain ⟨Bx3, hBx3⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (q3 x D D2 Dv DL) Bx2 out3 := ⟨_, rfl⟩
  rw [← hBx3] at s3
  have k3 : ∀ i : Fin (STx x D D2 Dv DL), i.val ≠ TT x + 1 → i.val < SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv →
      Bx3 i = Bx2 i := by
    intro i h1 hi
    rw [hBx3, inst_keep _ _ _ _ (fun j => by
      rcases q3_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with e | e <;> omega)]
  have o8' : Bx3 (TC x D D2 Dv DL) = List.replicate (2 ^ m) true := by
    have hq : q3 x D D2 Dv DL 8 = TC x D D2 Dv DL := by unfold q3; rw [if_neg (by decide), if_pos rfl]
    rw [hBx3, ← hq, install_slot _ q3_inj]
    exact o8
  have o9' : Bx3 (TE x D D2 Dv DL) = List.replicate (2 ^ m) true := by
    have hq : q3 x D D2 Dv DL 9 = TE x D D2 Dv DL := by
      unfold q3; rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    rw [hBx3, ← hq, install_slot _ q3_inj]
    exact o9
  -- 4
  obtain ⟨out4, s4, o4⟩ := x4_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) CL (2 ^ m) Bx3 o9'
    (fun k hk => by
      have hk0 : k.val ≠ 0 := fun e => hk (Fin.ext e)
      rw [hBx3, inst_keep _ _ _ _ (fun j => by
        rcases q3_cases (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with
            ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, e⟩ | ⟨-, -, -, e⟩ <;> rw [e]
        · simp only [TS_val, e6_val]; omega
        · simp only [TC_val, e6_val]; omega
        · simp only [TE_val, e6_val]; omega
        · rw [ca_val, e6_val]; have := j.isLt; omega)]
      rw [k2' (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [e6_val]; omega), k1' (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) k) (by simp only [e6_val]; omega)]
      exact b0hi _ (by simp only [e6_val]; omega))
  rw [hb] at o4
  obtain ⟨Bx4, hBx4⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install (e6 (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)) Bx3 out4 :=
    ⟨_, rfl⟩
  rw [← hBx4] at s4
  have k4 : ∀ i : Fin (STx x D D2 Dv DL), i.val < SD x D D2 + SD x D D2 + UnaryCalc.tapes Dv + NUn + 12 →
      Bx4 i = Bx3 i := by
    intro i hi
    rw [hBx4, inst_keep _ _ _ _ (fun j => by
      simp only [e6_val]; omega)]
  have o4' : Bx4 (TO x D D2 Dv DL) = List.replicate b true := by
    rw [hBx4, show TO x D D2 Dv DL = e6 (UnaryCalc.outputTape DL) from rfl, install_slot _ e6_inj]
    exact o4
  -- 5
  have hK4 : Bx4 (TK x D D2 Dv DL) = [] := by
    have vK := TK_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    rw [k4 (TK x D D2 Dv DL) (lt_of_lt_of_le TK_lt sd_le3), k3 (TK x D D2 Dv DL) (by rw [TK_val]; omega) (lt_of_lt_of_le TK_lt sd_le2),
      k2 (TK x D D2 Dv DL) (by rw [TK_val]; omega) (lt_of_lt_of_le TK_lt (Nat.le_add_right _ _)), k1 (TK x D D2 Dv DL) TK_lt]
    exact b0lo_ge _ (by simp only [kT_val]; omega)
  have s5 := x5_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) b Bx4 o4' hK4
  obtain ⟨Bx5, hBx5⟩ : ∃ B : Fin (STx x D D2 Dv DL) → List Bool, B = install ![TO x D D2 Dv DL, TK x D D2 Dv DL] Bx4
      (fun i => if i.val = 0 then List.replicate b true else RepairSource.VerifierDecoding.CompareMachine.word b) :=
    ⟨_, rfl⟩
  rw [← hBx5] at s5
  have k5 : ∀ i : Fin (STx x D D2 Dv DL), i.val ≠ (TK x D D2 Dv DL).val → i.val < SD x D D2 → Bx5 i = Bx4 i := by
    intro i hk hi
    rw [hBx5, inst_keep _ _ _ _ (fun j => by
      rcases q5_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) j with e | e <;> rw [e]
      · simp only [TO_val]; omega
      · exact fun e' => hk e'.symm)]
  -- the low region through stages 1–5
  have keep : ∀ i : Fin (SD x D D2), i.val ≠ 0 → i.val ≠ TT x + 1 →
      i.val ≠ TT x + 1 + Scrub.wk D + 2 → Bx5 (lo i) = Bx0 (lo i) := by
    intro i h0 h1 hk
    have hl := lo_lt (Dv := Dv) (DL := DL) i
    rw [k5 (lo (Dv := Dv) (DL := DL) i) (by rw [TK_val, lo_val]; exact hk) hl, k4 (lo (Dv := Dv) (DL := DL) i) (lt_of_lt_of_le hl sd_le3), k3 (lo (Dv := Dv) (DL := DL) i) (by rw [lo_val]; exact h1) (lt_of_lt_of_le hl sd_le2),
      k2 (lo (Dv := Dv) (DL := DL) i) (by rw [lo_val]; exact h0) (lt_of_lt_of_le hl (Nat.le_add_right _ _)), k1 (lo (Dv := Dv) (DL := DL) i) hl]
  -- 6
  have hcs1 : Bx5 (lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1)) = [false] := by
    rw [keep (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1) (by rw [cs1_val]; omega) (by rw [cs1_val]; omega) (by rw [cs1_val]; omega), b0lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 1) (by
      have := cs_lt (x := x) (D := D) (D1 := 0) (D2 := D2) 1; omega), e1]
  have s6 := x6_step (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL) Bx5 hcs1
  refine ⟨Bx5, (((((s0.seq s1).seq s2).seq s3).seq s4).seq s5).seq s6 |>.enlarge (by unfold bootXCostG; omega),
    ?_, hcs1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the request
    have v0 := T0_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    have vK := TK_val (x := x) (D := D) (D2 := D2) (Dv := Dv) (DL := DL)
    show Bx5 (T0 x D D2 Dv DL) = _
    rw [k5 (T0 x D D2 Dv DL) (by omega) T0_lt, k4 (T0 x D D2 Dv DL) (lt_of_lt_of_le T0_lt sd_le3), k3 (T0 x D D2 Dv DL) (by omega) (lt_of_lt_of_le T0_lt sd_le2)]
    exact i2'
  · rw [keep (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 2) (by rw [cs2_val]; omega) (by rw [cs2_val]; omega) (by rw [cs2_val]; omega), b0lo (cs (x := x) (D := D) (D1 := 0) (D2 := D2) 2) (by
      have := cs_lt (x := x) (D := D) (D1 := 0) (D2 := D2) 2; omega), e2]
  · intro c hc
    have hne : c ≠ sTape (sk x 0) := by intro e; subst e; simp [kept] at hc
    have hv : c.val ≠ 0 := by
      intro e
      apply hne
      apply Fin.ext
      rw [e]; rfl
    have hlt := c.isLt
    rw [keep (cT (D := D) (D1 := 0) (D2 := D2) c) (by rw [cT_val]; exact hv) (by simp only [cT_val]; omega) (by simp only [cT_val]; omega),
      b0lo (cT (D := D) (D1 := 0) (D2 := D2) c) (by simp only [cT_val]; omega)]
    exact escr c hc
  · intro j
    by_cases hj : j = Fin.castAdd 1 (UnaryCalc.inputTape D)
    · subst hj
      show Bx5 (TC x D D2 Dv DL) = _
      rw [k5 (TC x D D2 Dv DL) (by rw [TK_val, TC_val]; omega) TC_lt, k4 (TC x D D2 Dv DL) (lt_of_lt_of_le TC_lt sd_le3), o8']
      simp only [Scrub.calcIn, Fin.addCases_left]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
    · have hj0 : j.val ≠ 0 := by
        intro e
        apply hj
        apply Fin.ext
        rw [e]; rfl
      have hlt := j.isLt
      rw [keep (wT (x := x) (D1 := 0) (D2 := D2) j) (by simp only [wT_val]; omega) (by simp only [wT_val]; omega) (by simp only [wT_val]; omega),
        b0lo_ge (wT (x := x) (D1 := 0) (D2 := D2) j) (by simp only [wT_val]; omega)]
      revert hj
      refine Fin.addCases (fun k => ?_) (fun u => ?_) j
      · intro hk
        have hk0 : k.val ≠ 0 := by
          intro e; apply hk; apply Fin.ext; simp only [Fin.val_castAdd]; rw [e]; rfl
        simp [Scrub.calcIn, RepairSource.ProjectionNormalization.DimensionPolynomial.input, hk0]
      · intro _
        simp [Scrub.calcIn]
  · rw [keep (lgT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [lgT_val]; omega) (by rw [lgT_val]; omega) (by rw [lgT_val]; omega),
      b0lo_ge (lgT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [lgT_val]; omega)]
  · rw [keep (drT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [drT_val]; omega) (by rw [drT_val]; omega) (by rw [drT_val]; omega),
      b0lo_ge (drT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by rw [drT_val]; omega)]
  · have e := install_slot (![TO x D D2 Dv DL, TK x D D2 Dv DL]) (ListMachine.Row.pair_inj TO_ne_TK) Bx4
      (fun i => if i.val = 0 then List.replicate b true else RepairSource.VerifierDecoding.CompareMachine.word b) 1
    rw [hBx5]
    exact e
  · rw [keep (dT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by simp only [dT_val]; omega) (by simp only [dT_val]; omega) (by simp only [dT_val]; omega),
      b0lo (dT (x := x) (D := D) (D1 := 0) (D2 := D2)) (by simp only [dT_val]; omega), edt]

end Boot

end NearCubicWires.WireExponent3_5.PrimAsm.ShellT
