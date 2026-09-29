import Proof.Wire_3_5.Primitive.SeedFix.TS4T

/-! # thrStage4U, part 10: the v4 data stage's core run

P3:2543-2558, 2596-2604, 2150-2157, 2220-2231, 3068-3084 (the THR call's numbers once per call, then the tables and the
slice lengths): from the stage's entry bank plus blank extra tapes, the core (`coreM`: the prep, W6, the
fill-inputs-tables, the hash writer, the collection) leaves the data word `dataWord (hashNums … ++ thrCounts Cs carriers)`
on `sOUT`, the request on `sIN`, the tables on `sSym 0 3` and `sCar k 3`:

* `m3Fuel`; **`m3_core`** (under the prep's needs `P0Need`, W6's `TF2Ok` and `need`).

Paper quantities of the main type: the data word `hashNums ++ thrCounts` (the THR numbers, then the slice lengths). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.style.longLine false

namespace NearCubicWires.WireExponent3_5.PrimT.TS4
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.DockW
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.Data
open NearCubicWires.WireExponent3_5.PrimAsm.SymLayout NearCubicWires.WireExponent3_5.PrimAsm.ThrData
open NearCubicWires.WireExponent3_5.Shared NearCubicWires.SupplierPipeline
open NearCubicWires.RepairOrdinary.Streaming (marks)

/-- The core's fuel: the prep, W6, the first three phases, the hash writer, the collection. -/
noncomputable def m3Fuel (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams) {n a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit n)
    (carriers : List (Stars.Carrier n)) (L W : ℕ) (hs : List ℕ) : ℕ :=
  (((2 * p0StageCost n cr h0 h1 Cδ C (ReqBridge.thrCodes Cs).length (carriers.map Stars.Carrier.code).length W W + 2) +
    1 + (2 * W6.numsT alg Dexp (n + (W + (n + 1) ^ 26) + capTOf cr n h0 h1 Cδ C) + 3) + 1 +
    preCost a' Cs carriers L W) + 1 + qhCost hs) + 1 +
    collectTailCost (carriers.map (·.length)) (PrimT.ThrTab.tupleG Cs).length

/-- **The v4 data stage's core run.** -/
theorem m3_core (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ)
    (h1 : ζ < 1 / 2) (Cδ : ℕ) (C : Ledger.CapParams)
    (P : StarParams) {a' : ℕ} (Cs : Fin a' → NormalizedThresholdThresholdCircuit P.n)
    (carriers : List (Stars.Carrier P.n)) (tl : List Bool) (L W : ℕ)
    (ha : a' ≤ 4) (hk : carriers.length ≤ 2) (hL : ∀ i, (Cs i).descriptionBits ≤ L)
    (hLX : ∀ X ∈ carriers, ∀ g ∈ X, g.encodingBits + 1 ≤ L) (h2 : 2 ≤ P.n + L)
    (hcN : natBitLength P.n + 1 ≤ 2 * W + 2) (hcA : 2 ^ (natBitLength a' + 1) ≤ 2 * W + 2)
    (hcK : 2 ^ (natBitLength carriers.length + 1) ≤ 2 * W + 2)
    (hcx : ∀ x ∈ ReqBridge.thrCodes Cs, 2 * (RepairRepresentation.natWord x).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcy : ∀ y ∈ carriers.map Stars.Carrier.code, 2 * (RepairRepresentation.natWord y).length + 2 + P.n + L ≤ 2 * W + 2)
    (hcu : 2 * (unaryList ((hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) ++ thrCounts Cs carriers)).length + 2 ≤ 2 * W + 2)
    (hd : ∀ i, (Cs i).descriptionBits ≤ (P.n + 1) ^ 26)
    (hKb : ∀ c ∈ ReqBridge.thrCodes Cs, natBitLength c ≤ W)
    (hN0 : P0Need W P.n h0 h1 Cδ C cr (ReqBridge.thrCodes Cs).length (carriers.map Stars.Carrier.code).length W)
    (hn1 : 1 ≤ P.n) (hc1 : 1 ≤ (capTOf cr P.n h0 h1 Cδ C))
    (hok : PrimThrW.TopFront2.TF2Ok Cs (carriers.map Stars.Carrier.code) (W + (P.n + 1) ^ 26))
    (hneed : W6.needW alg Dexp (P.n + (capTOf cr P.n h0 h1 Cδ C)) ≤ (W + (P.n + 1) ^ 26)) :
    ∃ (H5 : Fin (TS + t4X alg) → ℕ) (A5 : Fin (TS + t4X alg) → List Bool),
      Step (coreM alg Dexp cr ζ Cδ C) (m3Fuel alg Dexp cr h0 h1 Cδ C Cs carriers L W (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C))) (fun _ => 0)
        (amb0 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W) H5 A5 ∧
      A5 (t4E alg (sTape sOUT)) = dataWord ((hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) ++ thrCounts Cs carriers) ∧
      A5 (t4E alg (sTape sIN)) = RepairOrdinary.frame (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      A5 (t4E alg (sTape (sSym 0 3))) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, A5 (t4E alg (sTape (sCar k 3))) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → A5 (t4E alg (sTape (sCar k 3))) = [] := by
  have hml : (carriers.map Stars.Carrier.code).length = carriers.length := List.length_map _
  have e3 := TS_val; have e4 := TI_w6x alg; have hb := t4X_ge alg
  -- 1: the prep
  refine (p0_step cr P.n h0 h1 Cδ C true (ReqBridge.thrCodes Cs)
    (carriers.map Stars.Carrier.code) tl W W hKb hN0).elim fun t0 hP0 => hP0.elim fun m0 hP => ?_
  have sP := hP.1
  have o0 := hP.2.1
  have o1 := hP.2.2.1
  have o3 := hP.2.2.2.1
  have o4 := hP.2.2.2.2.1
  have o5 := hP.2.2.2.2.2
  rw [hml] at o3
  have dP := sP.dock (t4P alg) (t4P_inj alg) (fun _ => 0) (amb0 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W) (fun _ => rfl) (matchP alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W)
  have eHP := dockH_existing (t4P alg) (fun _ => (0 : ℕ)) (fun _ => 0) (fun _ => rfl)
  replace dP := dP.congr eHP rfl
  -- 2: W6
  refine (W6.numsW6_run alg Dexp P Cs (carriers.map Stars.Carrier.code) tl carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26)
    hn1 ha hd hk hc1 hok hneed).elim fun J6 hW6 => ?_
  have sW := hW6.2
  have dW := sW.dock (t4W alg) (t4W_inj alg) (fun _ => 0) (amb1 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W (Fin.addCases t0 (fun _ : Fin 1 => List.replicate m0 false))) (fun _ => rfl)
    (matchW alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) t0 m0 o0 o3 o4 o5)
  have eHW := dockH_existing (t4W alg) (fun _ => (0 : ℕ)) (fun _ => 0) (fun _ => rfl)
  replace dW := dW.congr eHW rfl
  -- 3: the first three phases
  refine (preA_step a' Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK hcx hcy).elim fun σ2 hA => ?_
  have sA := hA.1
  have fx := hA.2.1
  have fx' := hA.2.2.1
  have fT := hA.2.2.2.1
  have fO := hA.2.2.2.2.1
  have fOh := hA.2.2.2.2.2.1
  have fOP := hA.2.2.2.2.2.2.1
  have fN := hA.2.2.2.2.2.2.2.1
  have fIN := hA.2.2.2.2.2.2.2.2.1
  have fTab := hA.2.2.2.2.2.2.2.2.2.1
  have fCar := hA.2.2.2.2.2.2.2.2.2.2.1
  have fCar' := hA.2.2.2.2.2.2.2.2.2.2.2
  have oW : (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6) ⟨0, by omega⟩ = RepairOrdinary.frame (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) := by
    rw [adc_lt _ _ 0 _ (by omega)]
    simp [PrimThrW.Nums3.nums3OutPorts, PrimThrW.NumsP.numsOutPorts]
  have dA := sA.dock (t4E alg) (t4E_inj alg) (fun _ => 0) (amb2 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W (Fin.addCases t0 (fun _ : Fin 1 => List.replicate m0 false)) (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6)) (fun _ => rfl)
    (matchA alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W t0 m0 o0 o1 (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6) oW)
  -- 4: the hash numbers
  have hlen := hashNums_length P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)
  have hu : (unaryList ((hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) ++ thrCounts Cs carriers)).length =
      (unaryList (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C))).length + (unaryList (thrCounts Cs carriers)).length := by
    rw [unaryList_append, List.length_append]
  have hv : ∀ i (h : i < 16), (σQ σ2 (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C))).st ⟨i + 1, by omega⟩ = List.replicate ((hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)).get ⟨i, by omega⟩) true ∧
      (σQ σ2 (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C))).sh ⟨i + 1, by omega⟩ = 0 := by
    intro i h
    refine ⟨?_, ?_⟩
    · simp only [σQ, show ¬ (i + 1 = 0) by omega, if_false, Nat.add_sub_cancel]
      rw [List.getD_eq_getElem _ _ (by omega)]
      rfl
    · simp [σQ]
  refine (qh_spec (2 * W + 2) (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) hlen (σQ σ2 (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C))) hv (by simp [σQ, fO])
    (by simp [σQ, fOh]) (by show σ2.val qOP = 0; exact fN) (by omega)).elim fun τQ hQ => ?_
  have eQ := hQ.1
  have q0 := hQ.2.1
  have q0h := hQ.2.2.1
  have qv := hQ.2.2.2.2.1
  have sQ := Exec.step (WExec.exec (2 * W + 2) eQ)
  have hWk : ∀ k (hk : k < 21 + (W6.TI alg + 1)), 1 ≤ k → k ≤ 16 →
      install (t4W alg) (amb1 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W (Fin.addCases t0 (fun _ : Fin 1 => List.replicate m0 false))) (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6) (t4W alg ⟨k, hk⟩) =
        List.replicate ((hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)).getD (k - 1) 0) true := by
    intro k hk a b
    rw [install_slot _ (t4W_inj alg), adc_lt _ _ k hk (by omega), nums3Out_hs _ _ _ _ _ k a b]
    rfl
  have dQ := sQ.dock (t4Q alg) (t4Q_inj alg) (dockH (t4E alg) (fun _ => 0) (wenc (2 * W + 2) σ2).H)
    (install (t4E alg) (amb2 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W (Fin.addCases t0 (fun _ : Fin 1 => List.replicate m0 false)) (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6)) (wenc (2 * W + 2) σ2).A) (matchQH alg (2 * W + 2) σ2 (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)))
    (matchQ alg (2 * W + 2) σ2 (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) (amb1 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W (Fin.addCases t0 (fun _ : Fin 1 => List.replicate m0 false))) (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6) hWk)
  -- 5: the collection
  have hne : ∀ s : Fin (DS + 1), s ≠ sOUT → (σC σ2 τQ).st s = σ2.st s ∧ (σC σ2 τQ).sh s = σ2.sh s := fun s hs => by
    simp [σC, Function.update_of_ne hs]
  refine (collectTail_spec (2 * W + 2) (σC σ2 τQ) (carriers.map (·.length))
    (PrimT.ThrTab.tupleG Cs).length (by simpa using hk)
    (fun k h => by
      rw [(hne _ (sCar_ne_low _ _ _ sOUT_low)).1, (hne _ (sCar_ne_low _ _ _ sOUT_low)).2,
        (hne _ (sCar_ne_low _ _ _ sOUT_low)).1, (hne _ (sCar_ne_low _ _ _ sOUT_low)).2]
      exact fx k h)
    (fun k h => by
      rw [(hne _ (sCar_ne_low _ _ _ sOUT_low)).1, (hne _ (sCar_ne_low _ _ _ sOUT_low)).2]
      exact fx' k h)
    (by rw [(hne _ (sSym_ne_low _ _ _ sOUT_low)).1, (hne _ (sSym_ne_low _ _ _ sOUT_low)).2]; exact fT)
    (by simp [σC]; exact q0h)
    (by show τQ.val rOP = 0; rw [qv rOP (by decide)]; exact fOP)
    (by
      have := hcu
      rw [hu, thrCounts, unaryList_append, List.length_append] at this
      omega)).elim fun τC hC => ?_
  have eC := hC.1
  have cOUT := hC.2.1
  have cst := hC.2.2.1
  have sC := Exec.step (WExec.exec (2 * W + 2) eC)
  have dC := sC.dock (t4E alg) (t4E_inj alg)
    (dockH (t4Q alg) (dockH (t4E alg) (fun _ => 0) (wenc (2 * W + 2) σ2).H) (wenc (2 * W + 2) τQ).H)
    (install (t4Q alg) (install (t4E alg) (amb2 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W (Fin.addCases t0 (fun _ : Fin 1 => List.replicate m0 false)) (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6)) (wenc (2 * W + 2) σ2).A) (wenc (2 * W + 2) τQ).A)
    (matchCH alg (2 * W + 2) σ2 τQ) (matchC alg (2 * W + 2) σ2 τQ (amb2 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W (Fin.addCases t0 (fun _ : Fin 1 => List.replicate m0 false)) (Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool) (PrimThrW.Nums3.nums3OutPorts (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) carriers.length (capTOf cr P.n h0 h1 Cδ C) (W + (P.n + 1) ^ 26) (PrimThrW.Joins.thrNumVals P Cs alg Dexp carriers.length (capTOf cr P.n h0 h1 Cδ C))) J6)))
  have core := (((dP.seq dW).seq dA).seq dQ).seq dC
  refine ⟨_, _, core, ?_, ?_, ?_, ?_, ?_⟩
  · rw [install_slot _ (t4E_inj alg), wenc_A_s, cOUT]
    have e0 : (σC σ2 τQ).st sOUT = τQ.st 0 := by simp [σC]
    rw [e0, q0, dataWord, ← RankBody.marks_frame, thrCounts]
    simp only [unaryList_append, WriteNat.marks_append, List.append_assoc, List.cons_append]
  · rw [install_slot _ (t4E_inj alg), wenc_A_s, cst _ (by decide), (hne _ (by decide)).1, fIN]
  · rw [install_slot _ (t4E_inj alg), wenc_A_s, cst _ (sSym_ne_low _ _ _ sOUT_low),
      (hne _ (sSym_ne_low _ _ _ sOUT_low)).1, fTab]
  · intro k h
    rw [install_slot _ (t4E_inj alg), wenc_A_s, cst _ (sCar_ne_low _ _ _ sOUT_low),
      (hne _ (sCar_ne_low _ _ _ sOUT_low)).1, fCar k h]
  · intro k h
    rw [install_slot _ (t4E_inj alg), wenc_A_s, cst _ (sCar_ne_low _ _ _ sOUT_low),
      (hne _ (sCar_ne_low _ _ _ sOUT_low)).1, fCar' k h]

end NearCubicWires.WireExponent3_5.PrimT.TS4
