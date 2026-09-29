import Proof.Wire_3_5.Primitive.SeedFix.C4GateThr

/-! # G3, the THR gate-frame writer, part 2: the budget and the writer at every call

"One-sided scores may be computed directly at a sampled row in polynomial time" (P3:3049-3050), within the
preprocessing class (`prim:runtime`, P3:3105-3115). G2's fill count (`CvS`, `DvS`: `needW` covers the THR codes' bits
and the tuple's occurrence count too) and G2's cost shape, with the THR data stage (`ThrDataStage2`) for the SYM
stage:

* `occ_len_le`, `tupleG_len_le` (the tuple's occurrences are at most its circuits' description bits);
  `thr_call_facts`, `thr_data_hyps` (the THR stage's hypotheses from `I.Call`);
* `pool_bounds3` (the THR pool and the three slots' widths are at most `3·DC`, `one_tape_support`);
* `DCn3`, `costN3`, `cost_le3`, `pb_costN3` (`gtC D`, `gtD D`);
* **`gateThrAt D hD`**: `GeoIface2.GateThrWriterAt l F E_G c_G kclk coef A a ha` under `gtD D ≤ E_G.Apre`,
  `gtC D·2^(gtD D) ≤ c_G` (the stage instance `D`, its tuple table on `sSym 0 3`).

Paper quantity of the main type: C3a's gate field of the THR call's pool (P3:1655-1664) within the preprocessing
class. -/

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
open NearCubicWires.PolynomialSchedule NearCubicWires.SourceInterfaces NearCubicWires.ValidatorPolynomialDomination

/-! ## The tuple's occurrences -/

theorem occ_len_le {n : ℕ} (C : NormalizedThresholdThresholdCircuit n) :
    (SupplierEstimator.thresholdCircuitOccurrences C).length ≤ C.descriptionBits := by
  unfold SupplierEstimator.thresholdCircuitOccurrences
  rw [List.length_ofFn]
  have h1 := Finset.card_le_univ C.top.support
  have h2 := PrimT.TabCost.thrDesc_pos C
  simp only [Finset.card_univ, Fintype.card_fin] at h1
  omega

theorem tupleG_len_le {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (B : ℕ)
    (h : ∀ i, (Cs i).descriptionBits ≤ B) : (PrimT.ThrTab.tupleG Cs).length ≤ a' * B := by
  unfold PrimT.ThrTab.tupleG
  rw [List.length_flatten, List.map_ofFn, List.sum_ofFn]
  calc ∑ i, (List.length ∘ fun j => (SupplierEstimator.thresholdCircuitOccurrences (Cs j)).map (·.gate)) i
      ≤ ∑ _i : Fin a', B := Finset.sum_le_sum (fun i _ => by
        show ((SupplierEstimator.thresholdCircuitOccurrences (Cs i)).map (·.gate)).length ≤ B
        rw [List.length_map]
        exact le_trans (occ_len_le _) (h i))
    _ = a' * B := by simp

/-! ## The THR stage's hypotheses at a call -/

section Data
variable {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n))

/-- **The THR stage's hypotheses** at `W ≥ needW n`, from the call's envelopes. -/
theorem thr_data_hyps (ha : a' ≤ 4) (hk : carriers.length ≤ 2) (hd : ∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26)
    (he : ∀ X ∈ carriers, X.WithinEnvelope 26) (W : ℕ) (hW : needW n ≤ W) :
    (∀ i, (Cs i).descriptionBits ≤ W) ∧ (∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ W) ∧ 2 ≤ n + W ∧
    natBitLength n + 1 ≤ 2 * W + 2 ∧ 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2 ∧
    2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2 ∧
    (∀ x ∈ PrimAsm.ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + n + W ≤ 2 * W + 2) ∧
    (∀ y ∈ carriers.map Stars.Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + n + W ≤ 2 * W + 2) ∧
    2 * (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2 ∧
    (∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ W) ∧
    (∀ X ∈ carriers, natBitLength X.code ≤ W) := by
  obtain ⟨p, hp⟩ : ∃ p, p = PrimAsm.CallSize.codeParam 26 26 n := ⟨_, rfl⟩
  have hpd : p = (n + 1) ^ 26 + (n + 1) ^ 26 + n + 4 := by rw [hp]; rfl
  have hWd : 4 * PrimAsm.CallSize.circBits p + 4 * PrimAsm.CallSize.carrierBits p + 20 * (n + 1) ^ 26 + 4 * n + 20 ≤
      W := by rw [hp]; exact hW
  have hcb : ∀ i, natBitLength (encodeNormalizedThresholdThresholdCircuit (Cs i)) ≤ PrimAsm.CallSize.circBits p :=
    fun i => PrimAsm.CallSize.code_bits_le .thr (Cs i) p (by omega)
      (by have := hd i; show (Cs i).descriptionBits ≤ p; omega)
  have hkb : ∀ X ∈ carriers, natBitLength X.code ≤ PrimAsm.CallSize.carrierBits p :=
    fun X hX => PrimAsm.CallSize.carrier_bits_le X 26 p (he X hX) (by omega)
  have hnN := PrimAsm.CopyNat.natBitLength_le_self_succ n
  refine ⟨fun i => by have := hd i; omega, fun X hX g hg => by have := (he X hX).2 g hg; omega, by omega,
    by omega, by have := nbl_small a' ha; omega, by have := nbl_small carriers.length (by omega); omega,
    fun x hx => ?_, fun y hy => ?_, ?_, fun i => by have := hcb i; omega, fun X hX => by have := hkb X hX; omega⟩
  · unfold PrimAsm.ReqBridge.thrCodes at hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    have := PrimAsm.CallSize.natWord_len_le (hcb i)
    omega
  · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hy
    have := PrimAsm.CallSize.natWord_len_le (hkb X hX)
    omega
  · have ht := tupleG_len_le Cs ((n + 1) ^ 26) hd
    have ht4 := Nat.mul_le_mul_right ((n + 1) ^ 26) ha
    have u := unaryList_len_le (PrimAsm.ThrData.thrCounts Cs carriers) (4 * (n + 1) ^ 26) (by
      intro c hc
      unfold PrimAsm.ThrData.thrCounts at hc
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨X, hX, rfl⟩ := List.mem_map.mp hc
        have := (he X hX).1
        omega
      · rw [List.mem_singleton] at hc
        rw [hc]
        omega)
    have hl : (PrimAsm.ThrData.thrCounts Cs carriers).length = carriers.length + 1 := by
      simp [PrimAsm.ThrData.thrCounts]
    rw [hl] at u
    have v := Nat.mul_le_mul_right (4 * (n + 1) ^ 26 + 1) (show carriers.length + 1 ≤ 3 by omega)
    omega

/-! ## The THR pool's size and the slots' widths -/

theorem gtH_nil (j : Fin 6) (hj : j ∈ thrJ) (h : gtG Cs carriers j = []) : gtH Cs carriers j = 1 := by
  have hj3 : j = 0 ∨ j = 1 ∨ j = 2 := by
    simp only [thrJ, List.mem_cons, List.not_mem_nil, or_false] at hj
    exact hj
  rcases hj3 with rfl | rfl | rfl
  · by_cases hk : (0 : Fin 6).val < carriers.length
    · rw [gtG_car Cs carriers 0 (by decide) hk] at h
      rw [gtH_car Cs carriers 0 (by decide) hk, maskGates_nil _ h]
      rfl
    · exact gtH_carE Cs carriers 0 (by decide) (by omega)
  · by_cases hk : (1 : Fin 6).val < carriers.length
    · rw [gtG_car Cs carriers 1 (by decide) hk] at h
      rw [gtH_car Cs carriers 1 (by decide) hk, maskGates_nil _ h]
      rfl
    · exact gtH_carE Cs carriers 1 (by decide) (by omega)
  · rw [gtG_two] at h
    rw [gtH_two, h]
    rfl

end Data

/-- **The THR pool's size and the slots' widths are at most `3·DC`**: every table is written within the stage's
`DC` steps. -/
theorem pool_bounds3 (D : PrimAsm.ThrData.ThrDataStage2) (hD : D.tabS = PrimAsm.Data.sSym 0 3) (P : Shared.StarParams)
    {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n) (carriers : List (Stars.Carrier P.n))
    (tl : List Bool) (L W : ℕ) (ha : a' ≤ 4) (hk : carriers.length ≤ 2)
    (hL : ∀ i, (Cs i).descriptionBits ≤ L) (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L)
    (h2 : 2 ≤ P.n + L)
    (hcN : natBitLength P.n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ PrimAsm.ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code,
      2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcu : 2 * (PrimAsm.Data.unaryList (PrimAsm.ThrData.thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2) :
    (PrimAsm.Records.thrPool P Cs carriers).length ≤ 3 * D.cost a' Cs carriers L W ∧
    gtHs Cs carriers ≤ 3 * D.cost a' Cs carriers L W + 3 := by
  obtain ⟨tout, m, sD, _, _, f1, f2, f4⟩ := D.run Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu
  obtain ⟨DC, hDC⟩ : ∃ x, x = D.cost a' Cs carriers L W := ⟨_, rfl⟩
  rw [← hDC] at sD ⊢
  have hlen : ∀ j : Fin 6, (tout (sTape (tabStream j))).length ≤ DC := by
    intro j
    obtain ⟨r, hr, _, hT, hs⟩ := sD
    have hv := tabStream_val j
    have hpos : 17 ≤ (tabStream j).val := by rw [hv]; split_ifs <;> omega
    have hne : ∀ s : Fin (PrimAsm.Data.DS + 1), s.val ≤ 3 →
        sTape (nr := PrimAsm.Data.DR) (tabStream j) ≠ sTape s :=
      fun s hs e => by have := congrArg Fin.val (sTape_inj e); omega
    have h0 := DecompositionSource.one_tape_support _ _ _ r (dPos (tabStream j)) 0 hr (le_refl _) (by
      show (Fin.addCases (motive := fun _ => List Bool)
        (PrimAsm.Data.rawIn (PrimAsm.Data.reqW P.n true (PrimAsm.ReqBridge.thrCodes Cs)
          (carriers.map Stars.Carrier.code) tl) P.n L W)
        (fun _ : Fin 1 => List.replicate 0 false) (dPos (tabStream j))).length ≤ 0
      rw [addCases_dPos]
      unfold PrimAsm.Data.rawIn
      rw [if_neg (hne PrimAsm.Data.sIN (by decide)), if_neg (hne PrimAsm.Data.sNT (by decide)),
        if_neg (hne PrimAsm.Data.sLT (by decide)), if_neg (hne PrimAsm.Data.sCT (by decide))]
      simp)
    rw [hT] at h0
    simp only [addCases_dPos] at h0
    omega
  have hG : ∀ j ∈ thrJ, (gtG Cs carriers j).length ≤ DC ∧ gtH Cs carriers j ≤ DC + 1 := by
    intro j hj
    by_cases hn : gtG Cs carriers j = []
    · refine ⟨by rw [hn]; simp, by rw [gtH_nil Cs carriers j hj hn]; omega⟩
    · rcases slot_T3 Cs carriers D.tabS hD tout f1 f2 f4 j hj with e | ⟨_, e⟩
      · have hl := hlen j
        rw [e] at hl
        obtain ⟨g1, g2⟩ := gatesW_len (gtH Cs carriers j) (gtG Cs carriers j)
        have := g2 hn
        omega
      · exact absurd e hn
  have hsum : (PrimAsm.Records.thrPool P Cs carriers).length = (gtG Cs carriers 0).length +
      (gtG Cs carriers 1).length + (gtG Cs carriers 2).length := by
    rw [thrPool_eq P Cs carriers hk, thrJ_flatMap]
    simp only [List.length_append]
  obtain ⟨a0, b0⟩ := hG 0 (by decide)
  obtain ⟨a1, b1⟩ := hG 1 (by decide)
  obtain ⟨a2, b2⟩ := hG 2 (by decide)
  refine ⟨by rw [hsum]; omega, by unfold gtHs; omega⟩

/-! ## The THR writer's steps -/

/-- The THR data stage's steps' bound at length `n`. -/
noncomputable def DCn3 (D : PrimAsm.ThrData.ThrDataStage2) (n : ℕ) : ℕ :=
  D.Cc * (UnaryCalc.value DvS CvS n + n + UnaryCalc.value DvS CvS n + UnaryCalc.value DvS CvS n + 1) ^ D.Dc

/-- **The THR writer's steps' bound at length `n`.** -/
noncomputable def costN3 (D : PrimAsm.ThrData.ThrDataStage2) (n : ℕ) : ℕ :=
  2 * (frontCn n + 1 + (2 * (UnaryCalc.value DvS CvS n * 7 + 1 + 1 + (n * 7 + 1)) + 2) + 1 + DCn3 D n + 1 +
    (2 * C4Gates.convCost n (3 * DCn3 D n) (3 * DCn3 D n + 3) + 2)) + 2

theorem cost_le3 (D : PrimAsm.ThrData.ThrDataStage2) (w : List Bool) (n DC P H : ℕ)
    (hw : w.length ≤ PrimAsm.CallSize.wordBound 26 26 2 n)
    (hDC : DC ≤ DCn3 D n) (hP : P ≤ 3 * DC) (hH : H ≤ 3 * DC + 3) :
    2 * gsCost w n DvS CvS DC P H + 2 ≤ costN3 D n := by
  have hc := convCost_mono (le_refl n) (show P ≤ 3 * DCn3 D n by omega) (show H ≤ 3 * DCn3 D n + 3 by omega)
  unfold gsCost frontC costN3 frontCn
  omega

theorem pb_DCn3 (D : PrimAsm.ThrData.ThrDataStage2) : PolynomiallyBounded (DCn3 D) :=
  polynomiallyBounded_mul (polynomiallyBounded_constant _)
    (polynomiallyBounded_pow (polynomiallyBounded_add (polynomiallyBounded_add (polynomiallyBounded_add
      (polynomiallyBounded_add pb_value polynomiallyBounded_id) pb_value) pb_value) (polynomiallyBounded_constant 1)) _)

theorem pb_conv3 (D : PrimAsm.ThrData.ThrDataStage2) :
    PolynomiallyBounded (fun n => C4Gates.convCost n (3 * DCn3 D n) (3 * DCn3 D n + 3)) := by
  have hD := pb_DCn3 D
  have hc := hD
  apply polynomiallyBounded_mono (fun n => convCost_le_maj n (3 * DCn3 D n) (3 * DCn3 D n + 3))
  unfold convMaj
  iterate 40 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible exact pb_value
    | with_reducible exact pb_nbl
    | with_reducible exact pb_power
    | with_reducible exact hD
    | with_reducible exact hc
    | with_reducible exact PrimAsm.CallSize.wordBound_poly
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

theorem pb_costN3 (D : PrimAsm.ThrData.ThrDataStage2) : PolynomiallyBounded (costN3 D) := by
  have hD := pb_DCn3 D
  have hc := pb_conv3 D
  show PolynomiallyBounded (fun n => costN3 D n)
  simp only [costN3, frontCn]
  iterate 40 (all_goals (try (first
    | with_reducible exact polynomiallyBounded_id
    | with_reducible exact polynomiallyBounded_constant _
    | with_reducible exact pb_value
    | with_reducible exact pb_nbl
    | with_reducible exact pb_power
    | with_reducible exact hD
    | with_reducible exact hc
    | with_reducible exact PrimAsm.CallSize.wordBound_poly
    | with_reducible apply polynomiallyBounded_add
    | with_reducible apply polynomiallyBounded_mul
    | with_reducible apply polynomiallyBounded_pow)))

/-- The THR writer's steps' coefficient. -/
noncomputable def gtC (D : PrimAsm.ThrData.ThrDataStage2) : ℕ := Classical.choose (pb_costN3 D)

/-- The THR writer's steps' degree. -/
noncomputable def gtD (D : PrimAsm.ThrData.ThrDataStage2) : ℕ :=
  Classical.choose (Classical.choose_spec (pb_costN3 D))

theorem costN3_le (D : PrimAsm.ThrData.ThrDataStage2) (n : ℕ) : costN3 D n ≤ gtC D * (n + 1) ^ gtD D :=
  (Classical.choose_spec (Classical.choose_spec (pb_costN3 D))).2 n

/-! ## The THR writer at every THR call -/

section Ready
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.Split NearCubicWires.WireExponent3_5.Primitive
open NearCubicWires.WireExponent3_5.PrimAsm.Plan
variable (l : Literals) (F : GateFree l) (EG : Envelope) (cG kclk coef A a : ℕ) (ha : a ≤ kclk + 1)

theorem thr_call_facts (n a' : ℕ) (ha' : a' ≤ 4) (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (h : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation)) :
    carriers.length ≤ 2 ∧ (∀ i, (Cs i).descriptionBits ≤ (n + 1) ^ 26) ∧ (∀ X ∈ carriers, X.WithinEnvelope 26) := by
  obtain ⟨_, hcar, hdesc, hcount, _, _, _⟩ := h
  exact ⟨hcount, fun i => hdesc i, hcar⟩

/-- **The THR gate-frame writer's run at every THR call of the family**, within the preprocessing class. -/
theorem gt_ready (D : PrimAsm.ThrData.ThrDataStage2) (hD : D.tabS = PrimAsm.Data.sSym 0 3)
    (hA : gtD D ≤ EG.Apre) (hc : gtC D * 2 ^ gtD D ≤ cG) (n a' : ℕ) (ha' : a' ≤ 4)
    (Cs : Fin a' → NormalizedThresholdThresholdCircuit n) (carriers : List (Stars.Carrier n)) (translation : List ℕ)
    (hcall : (callInputs l F kclk coef A a ha).Call (thrReq n a' ha' Cs carriers translation))
    (hs : (callInputs l F kclk coef A a ha).StarAt n) :
    PrimAsm.WriterIfaceJ.WriterRun (mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).M
      (cG * classBound EG .preprocessing n (((gate0 l F).budget kclk coef A a ha).kOf n)
        (((gate0 l F).budget kclk coef A a ha).psiOf n))
      (mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).inS
      (mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS)).outS
      (thrReq n a' ha' Cs carriers translation).word
      (C4Geo.gateField (PrimAsm.Records.thrPool ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers)) := by
  refine stage_run (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS) _ _ _ ?_
  obtain ⟨hk, hd, he⟩ := thr_call_facts l F kclk coef A a ha n a' ha' Cs carriers translation hcall
  have hn : 1 ≤ n := by
    have h1 := hs.2.1
    have h2 := hs.2.2.1
    omega
  obtain ⟨hL, hLX, h2, hcN, hcA, hcK, hcx, hcy, hcu, hK, hKX⟩ :=
    thr_data_hyps Cs carriers ha' hk hd he (UnaryCalc.value DvS CvS n) (needW_le n)
  have hword : PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation) = (thrReq n a' ha' Cs carriers translation).word := by
    have := PrimAsm.ReqBridge.reqW_thrReq ha' Cs carriers translation []
    simpa using this
  rw [← hword]
  refine gt_run D hD DvS CvS _ ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers _ ha' hk _ rfl
    hL hLX h2 hcN hcA hcK hcx hcy hcu ?_
  obtain ⟨hP, hH⟩ := pool_bounds3 D hD ((callInputs l F kclk coef A a ha).starParams n hs) Cs carriers
    (RepairRepresentation.natListWord translation) _ _ ha' hk hL hLX h2 hcN hcA hcK hcx hcy hcu
  have hDC := D.cost_le Cs carriers (UnaryCalc.value DvS CvS n) (UnaryCalc.value DvS CvS n)
    (UnaryCalc.value DvS CvS n) ha' hk hL hLX hK hKX h2
  have hwl : (PrimAsm.Data.reqW n true (PrimAsm.ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code)
      (RepairRepresentation.natListWord translation)).length ≤ PrimAsm.CallSize.wordBound 26 26 2 n := by
    rw [hword]
    exact PrimAsm.CallSize.gate_word_length_le l F kclk coef A a ha _ hcall
  have c1 := cost_le3 D _ n _ _ _ hwl (by unfold DCn3; exact hDC) hP hH
  have c2 := costN3_le D n
  have c3 := pre_class_le EG (gtC D) (gtD D) cG n (((gate0 l F).budget kclk coef A a ha).kOf n)
    (((gate0 l F).budget kclk coef A a ha).psiOf n) hn hA hc
  exact le_trans c1 (le_trans c2 c3)

/-- **The THR gate-frame writer** (`GeoIface2.GateThrWriterAt`): the machine `gtM D DvS CvS`, from
`frame (thrReq …).word` to C3a's gate field of the THR call's pool, at every call of the family (`a' = 0` included). -/
noncomputable def gateThrAt (D : PrimAsm.ThrData.ThrDataStage2) (hD : D.tabS = PrimAsm.Data.sSym 0 3)
    (hA : gtD D ≤ EG.Apre) (hc : gtC D * 2 ^ gtD D ≤ cG) :
    GeoIface2.GateThrWriterAt l F EG cG kclk coef A a ha :=
  ⟨mkStage (gtM D DvS CvS) (gsIn DvS) (gsOut DvS) (gsIn_ne_out DvS), fun n a' ha' Cs carriers translation hcall hs =>
    gt_ready l F EG cG kclk coef A a ha D hD hA hc n a' ha' Cs carriers translation hcall hs⟩

end Ready

end NearCubicWires.WireExponent3_5.PrimT.C4GateSym
