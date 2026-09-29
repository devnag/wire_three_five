import Proof.Wire_3_5.Primitive.SeedFix.TS4U

/-! # thrStage4U, part 11: the v4 machine's run (the reset and the tape order of `ThrDataStage4`)

P3:2543-2558, 3068-3084 (as part 10): PA's masked reset returns every head to `0` and appends its junk tape; the slot
permutation `t4perm` puts that tape at position `DS + 2 + DR` and the extra tapes after it, the order of
`ThrDataStage4.M3 : Machine (DS + 2 + DR + 1 + x3) s3`:

* **`m3_run`**: `ThrDataStage4.run3`'s conclusion for `m3M` (with `x3 = t4X alg = thrStageRoom alg`) at fuel
  `2·m3Fuel + 2`, the extra tapes' contents within the fuel plus one.

Paper quantities of the main type: the data word `hashNums ++ thrCounts`, the request, the tables. -/

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

section Perm
variable (alg : RepairRepresentation.DecompositionAlgorithm)

theorem t4perm_val (j : Fin (TS + t4X alg + 1)) : (t4perm alg j).val =
    if j.val < TS then j.val else if j.val < TS + t4X alg then j.val + 1 else TS := rfl

theorem t4perm_lt (j : Fin (TS + t4X alg + 1)) (h : j.val < TS) : (t4perm alg j).val = j.val := by
  rw [t4perm_val, if_pos h]

theorem t4perm_mid (j : Fin (TS + t4X alg + 1)) (h1 : ¬ j.val < TS) (h2 : j.val < TS + t4X alg) :
    (t4perm alg j).val = j.val + 1 := by
  rw [t4perm_val, if_neg h1, if_pos h2]

theorem t4perm_last (j : Fin (TS + t4X alg + 1)) (h2 : ¬ j.val < TS + t4X alg) : (t4perm alg j).val = TS := by
  have h1 : ¬ j.val < TS := by omega
  rw [t4perm_val, if_neg h1, if_neg h2]

/-- The reset's output in `ThrDataStage4`'s tape order. -/
theorem perm_out (A5 : Fin (TS + t4X alg) → List Bool) (m : ℕ) (INP : Fin (TS + 1 + t4X alg) → List Bool) :
    install (t4perm alg) INP (Fin.addCases (m := TS + t4X alg) (n := 1) (motive := fun _ => List Bool) A5
      (fun _ : Fin 1 => List.replicate m false)) =
    Fin.addCases (m := DS + 2 + DR + 1) (n := t4X alg) (motive := fun _ => List Bool)
      (Fin.addCases (fun i => A5 (t4E alg i)) (fun _ : Fin 1 => List.replicate m false))
      (fun e => A5 ⟨TS + e.val, by have := e.isLt; omega⟩) := by
  funext t
  have ht := t.isLt
  have e3 := TS_val; have eD := DS_val; have eR := DR_val
  by_cases h1 : t.val < TS
  · have hs := install_slot (t4perm alg) (t4perm_inj alg) INP (Fin.addCases (m := TS + t4X alg) (n := 1)
      (motive := fun _ => List Bool) A5 (fun _ : Fin 1 => List.replicate m false)) ⟨t.val, by omega⟩
    have ep : t4perm alg ⟨t.val, by omega⟩ = t := Fin.ext (t4perm_lt alg _ h1)
    rw [ep] at hs
    rw [hs, adc_lt _ _ t.val _ (by omega), adc_lt _ _ t.val ht (by omega), adc_lt _ _ t.val _ (by omega)]
    rfl
  by_cases h2 : t.val = TS
  · have hs := install_slot (t4perm alg) (t4perm_inj alg) INP (Fin.addCases (m := TS + t4X alg) (n := 1)
      (motive := fun _ => List Bool) A5 (fun _ : Fin 1 => List.replicate m false)) ⟨TS + t4X alg, by omega⟩
    have ep : t4perm alg ⟨TS + t4X alg, by omega⟩ = t := Fin.ext (by rw [t4perm_last alg _ (by simp)]; omega)
    rw [ep] at hs
    rw [hs, adc_ge _ _ (TS + t4X alg) _ le_rfl, adc_lt _ _ t.val ht (by omega), adc_ge _ _ t.val _ (by omega)]
  · have hs := install_slot (t4perm alg) (t4perm_inj alg) INP (Fin.addCases (m := TS + t4X alg) (n := 1)
      (motive := fun _ => List Bool) A5 (fun _ : Fin 1 => List.replicate m false)) ⟨t.val - 1, by omega⟩
    have ep : t4perm alg ⟨t.val - 1, by omega⟩ = t := Fin.ext (by
      rw [t4perm_mid alg _ (by simp; omega) (by simp; omega)]; simp; omega)
    rw [ep] at hs
    rw [hs, adc_lt _ _ (t.val - 1) _ (by omega), adc_ge _ _ t.val ht (by omega)]
    congr 1
    ext
    simp
    omega

end Perm

/-- **The v4 machine's run.** -/
theorem m3_run (alg : RepairRepresentation.DecompositionAlgorithm) (Dexp cr : ℕ) {ζ : ℚ} (h0 : 0 < ζ)
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
    ∃ (tout : Fin (DS + 2 + DR) → List Bool) (m : ℕ) (J : Fin (t4X alg) → List Bool),
      Step (m3M alg Dexp cr ζ Cδ C) (2 * m3Fuel alg Dexp cr h0 h1 Cδ C Cs carriers L W (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) + 2) (fun _ => 0) (Fin.addCases (m := DS + 2 + DR + 1) (n := t4X alg) (motive := fun _ => List Bool) (Fin.addCases (rawIn (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => [])) (fun _ => 0)
        (Fin.addCases (m := DS + 2 + DR + 1) (n := t4X alg) (motive := fun _ => List Bool)
          (Fin.addCases tout (fun _ : Fin 1 => List.replicate m false)) J) ∧
      (∀ j, (J j).length ≤ (2 * m3Fuel alg Dexp cr h0 h1 Cδ C Cs carriers L W (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) + 2) + 1) ∧
      tout (sTape sOUT) = dataWord ((hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) ++ thrCounts Cs carriers) ∧
      tout (sTape sIN) = RepairOrdinary.frame (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) ∧
      tout (sTape (sSym 0 3)) = (if a' = 0 then [] else
        FinalPass.Corner.gatesW (PrimT.tabH (PrimT.ThrTab.tupleG Cs)) (PrimT.ThrTab.tupleG Cs)) ∧
      (∀ k : Fin 2, ∀ h : k.val < carriers.length, tout (sTape (sCar k 3)) =
        FinalPass.Corner.gatesW (PrimT.tabH (carriers.get ⟨k.val, h⟩))
          (FinalPass.Corner.maskGates (carriers.get ⟨k.val, h⟩))) ∧
      ∀ k : Fin 2, carriers.length ≤ k.val → tout (sTape (sCar k 3)) = [] := by
  have e3 := TS_val; have hb := t4X_ge alg
  refine (m3_core alg Dexp cr h0 h1 Cδ C P Cs carriers tl L W ha hk hL hLX h2 hcN hcA hcK hcx hcy hcu hd hKb hN0
    hn1 hc1 hok hneed).elim fun H5 hc0 => hc0.elim fun A5 hc => ?_
  have core := hc.1
  refine (ListMachine.Row.maskBlank core (fun _ => true) (fun _ _ => rfl) 0).elim fun m hm => ?_
  have hH : ∀ j, (fun _ => (0 : ℕ)) (t4perm alg j) =
      Fin.addCases (m := TS + t4X alg) (n := 1) (motive := fun _ => ℕ) (fun _ => 0) (fun _ => 0) j := by
    intro j
    refine Fin.addCases (fun a => ?_) (fun u => ?_) j <;> simp
  have hA : ∀ j, (Fin.addCases (m := DS + 2 + DR + 1) (n := t4X alg) (motive := fun _ => List Bool) (Fin.addCases (rawIn (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => [])) (t4perm alg j) =
      Fin.addCases (m := TS + t4X alg) (n := 1) (motive := fun _ => List Bool) (amb0 alg (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W)
        (fun _ : Fin 1 => List.replicate 0 false) j := by
    intro j
    have hj := j.isLt
    have eD := DS_val; have eR := DR_val
    by_cases h1' : j.val < TS
    · have ep : t4perm alg j = ⟨j.val, by omega⟩ := Fin.ext (t4perm_lt alg j h1')
      rw [ep, adc_lt _ _ j.val _ (by omega), adc_lt _ _ j.val _ (by omega), adc_lt _ _ j.val hj (by omega),
        amb0_lt alg _ _ _ _ j.val _ h1']
    by_cases h2' : j.val < TS + t4X alg
    · have ep : t4perm alg j = ⟨j.val + 1, by omega⟩ := Fin.ext (t4perm_mid alg j h1' h2')
      rw [ep, adc_ge _ _ (j.val + 1) _ (by omega), adc_lt _ _ j.val hj h2', amb0_ge alg _ _ _ _ j.val _ (by omega)]
    · have ep : t4perm alg j = ⟨TS, by omega⟩ := Fin.ext (t4perm_last alg j h2')
      rw [ep, adc_lt _ _ TS _ (by omega), adc_ge _ _ TS _ (by omega), adc_ge _ _ j.val hj (by omega)]
  have d := hm.dock (t4perm alg) (t4perm_inj alg) (fun _ => 0) (Fin.addCases (m := DS + 2 + DR + 1) (n := t4X alg) (motive := fun _ => List Bool) (Fin.addCases (rawIn (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => [])) hH hA
  have eH : dockH (t4perm alg) (fun _ => (0 : ℕ))
      (Fin.addCases (m := TS + t4X alg) (n := 1) (motive := fun _ => ℕ) (fun i => if (fun _ => true) i then 0 else H5 i)
        (fun _ => 0)) = fun _ => 0 :=
    dockH_existing _ _ _ (fun j => by refine Fin.addCases (fun a => ?_) (fun u => ?_) j <;> simp)
  have d2 := d.congr eH rfl
  have pe := perm_out alg A5 m (Fin.addCases (m := DS + 2 + DR + 1) (n := t4X alg) (motive := fun _ => List Bool) (Fin.addCases (rawIn (reqW P.n true (ReqBridge.thrCodes Cs) (carriers.map Stars.Carrier.code) tl) P.n L W) (fun _ : Fin 1 => List.replicate 0 false)) (fun _ => []))
  have fin := d2.congr rfl pe
  refine ⟨fun i => A5 (t4E alg i), m, fun e => A5 ⟨TS + e.val, by have := e.isLt; omega⟩, fin, ?_, hc.2.1, hc.2.2.1,
    hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2⟩
  intro e
  have hl := Step.tape_length fin (Fin.natAdd (DS + 2 + DR + 1) e) 0 0 (le_refl _)
    (by rw [Fin.addCases_right]; exact le_refl _)
  rw [Fin.addCases_right] at hl
  have hmx : max 0 (0 + (2 * m3Fuel alg Dexp cr h0 h1 Cδ C Cs carriers L W (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) + 2) + 1) = (2 * m3Fuel alg Dexp cr h0 h1 Cδ C Cs carriers L W (hashNums P Cs carriers alg Dexp (capTOf cr P.n h0 h1 Cδ C)) + 2) + 1 := by omega
  rw [hmx] at hl
  exact hl

end NearCubicWires.WireExponent3_5.PrimT.TS4
