import Proof.Wire_3_5.Primitive.SeedFix.TS4M

/-! # thrStage4U, part 7: the docks' inputs match (the prep, W6, the first three phases)

P3:2543-2558, 3068-3084 (as part 6): each stage of `coreM` starts on exactly the tapes its run lemma names:
* `rawIn_val`, `rawS_val` (the entry banks by index);
* **`matchP`** (the prep on the stage's entry bank plus blank extra tapes), **`matchW`** (W6 on the request, the prep's
  `1^{|carriers|}`, `1^{cap_T}`, `1^V`, everything else blank), **`matchA`** (the stage's own tapes are its entry bank
  again: the prep and W6 put back the request and the fill count).

Paper quantities of the main type: the data stage's entry bank and W6's in-ports (the request, `|carriers|`, `cap_T`,
`V`). -/

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

theorem rawIn_val (w : List Bool) (n L W : ℕ) (j : Fin (DS + 2 + DR)) : rawIn w n L W j =
    if j.val = 0 then RepairOrdinary.frame w else if j.val = 2 then List.replicate n true
    else if j.val = 3 then List.replicate L true else if j.val = 4 then List.replicate W true else [] := by
  simp only [rawIn, Fin.ext_iff, sTape, sIN, sNT, sLT, sCT]
  simp [Nat.mod_eq_of_lt (show 2 < DS + 1 by decide), Nat.mod_eq_of_lt (show 3 < DS + 1 by decide),
    Nat.mod_eq_of_lt (show 1 < DS + 1 by decide)]

theorem rawS_val (w : List Bool) (W : ℕ) (j : Fin (LNS 0 + 2 + LNR)) : rawS w W j =
    if j.val = 0 then RepairOrdinary.frame w else if j.val = 2 then List.replicate W true else [] := by
  simp only [rawS, Fin.ext_iff, sTape, sk]
  simp

variable (alg : RepairRepresentation.DecompositionAlgorithm)

/-- The stage's entry bank plus blank extra tapes. -/
def amb0 (w : List Bool) (n L W : ℕ) : Fin (TS + t4X alg) → List Bool :=
  Fin.addCases (rawIn w n L W) (fun _ => [])

theorem amb0_lt (w : List Bool) (n L W v : ℕ) (hv : v < TS + t4X alg) (h : v < TS) :
    amb0 alg w n L W ⟨v, hv⟩ = rawIn w n L W ⟨v, h⟩ := adc_lt _ _ v hv h

theorem amb0_ge (w : List Bool) (n L W v : ℕ) (hv : v < TS + t4X alg) (h : TS ≤ v) :
    amb0 alg w n L W ⟨v, hv⟩ = [] := by
  unfold amb0; rw [adc_ge _ _ v hv h]

/-- **The prep's input**: the request on `sIN`, `1^W` on `sCT`, blank elsewhere. -/
theorem matchP (w : List Bool) (n L W : ℕ) (j : Fin (LNS 0 + 2 + LNR + 1)) :
    amb0 alg w n L W (t4P alg j) = Fin.addCases (rawS w W) (fun _ : Fin 1 => List.replicate 0 false) j := by
  have hj := j.isLt
  have e1 := LNS0_val; have e2 := LNR_val; have e3 := TS_val
  by_cases h0 : j.val = 0
  · have ep : t4P alg j = ⟨0, by omega⟩ := Fin.ext (by simp [t4P, h0])
    rw [ep, amb0_lt alg w n L W 0 _ (by omega), rawIn_val, adc_lt _ _ j.val hj (by omega), rawS_val]
    simp [h0]
  by_cases h2 : j.val = 2
  · have ep : t4P alg j = ⟨4, by omega⟩ := Fin.ext (by simp [t4P, h2])
    rw [ep, amb0_lt alg w n L W 4 _ (by omega), rawIn_val, adc_lt _ _ j.val hj (by omega), rawS_val]
    simp [h2]
  · have ep : t4P alg j = ⟨TS + (t4b alg + j.val), by have := t4X_ge alg; omega⟩ := Fin.ext (by simp [t4P, h0, h2])
    rw [ep, amb0_ge alg w n L W _ _ (by omega)]
    by_cases hl : j.val < LNS 0 + 2 + LNR
    · rw [adc_lt _ _ j.val hj hl, rawS_val]; simp [h0, h2]
    · rw [adc_ge _ _ j.val hj (by omega)]; rfl

/-- The tapes after the prep. -/
noncomputable def amb1 (w : List Bool) (n L W : ℕ) (out0 : Fin (LNS 0 + 2 + LNR + 1) → List Bool) :
    Fin (TS + t4X alg) → List Bool :=
  install (t4P alg) (amb0 alg w n L W) out0

theorem t4P_ne_t4W_small (j' : Fin (LNS 0 + 2 + LNR + 1)) (j : Fin (21 + (W6.TI alg + 1)))
    (h1 : j.val ≠ 0) (h2 : j.val ≠ 1) (h3 : j.val ≠ 2) (h4 : j.val ≠ 20) : t4P alg j' ≠ t4W alg j := by
  intro e
  have hv := congrArg Fin.val e
  simp only [t4P, t4W] at hv
  have := TI_w6x alg; have := j.isLt; have := j'.isLt; have := TS_val
  unfold t4b at hv
  split_ifs at hv <;> omega

/-- **W6's input**: the request on port `0`, the prep's `1^{|cc|}`, `1^{cap_T}`, `1^V` on ports `1`, `2`, `20`, blank
elsewhere. -/
theorem matchW (w : List Bool) (n L W ncar capT V : ℕ) (tout0 : Fin (LNS 0 + 2 + LNR) → List Bool) (m0 : ℕ)
    (o0 : tout0 (sTape (sk 0 0)) = RepairOrdinary.frame w) (o3 : tout0 (sTape (sk 0 3)) = List.replicate ncar true)
    (o4 : tout0 (sTape (sk 0 4)) = List.replicate capT true) (o5 : tout0 (sTape (sk 0 5)) = List.replicate V true)
    (j : Fin (21 + (W6.TI alg + 1))) :
    amb1 alg w n L W (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m0 false)) (t4W alg j) =
      Fin.addCases (m := 21) (n := W6.TI alg + 1) (motive := fun _ => List Bool)
        (PrimThrW.Nums3.nums3InPorts w ncar capT V) (fun _ => []) j := by
  have hj := j.isLt
  have e1 := LNS0_val; have e2 := LNR_val; have e3 := TS_val; have e4 := TI_w6x alg
  have hb := t4X_ge alg
  unfold amb1
  have slotP : ∀ (k : ℕ) (hk : k < LNS 0 + 2 + LNR), t4W alg j = t4P alg ⟨k, by omega⟩ →
      install (t4P alg) (amb0 alg w n L W) (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m0 false)) (t4W alg j) =
        tout0 ⟨k, hk⟩ := by
    intro k hk e
    rw [e, install_slot _ (t4P_inj alg), adc_lt _ _ k (by omega) hk]
  by_cases h0 : j.val = 0
  · rw [slotP 0 (by omega) (Fin.ext (by simp [t4P, t4W, h0])), adc_lt _ _ j.val hj (by omega)]
    have e : (⟨0, by omega⟩ : Fin (LNS 0 + 2 + LNR)) = sTape (sk 0 0) := Fin.ext (by simp [sTape, sk])
    rw [e, o0]
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, h0]
  by_cases h1 : j.val = 1
  · rw [slotP 4 (by omega) (Fin.ext (by simp [t4P, t4W, h1])), adc_lt _ _ j.val hj (by omega)]
    have e : (⟨4, by omega⟩ : Fin (LNS 0 + 2 + LNR)) = sTape (sk 0 3) := Fin.ext (by simp [sTape, sk])
    rw [e, o3]
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, h1]
  by_cases h2 : j.val = 2
  · rw [slotP 5 (by omega) (Fin.ext (by simp [t4P, t4W, h2])), adc_lt _ _ j.val hj (by omega)]
    have e : (⟨5, by omega⟩ : Fin (LNS 0 + 2 + LNR)) = sTape (sk 0 4) := Fin.ext (by simp [sTape, sk])
    rw [e, o4]
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, h2]
  by_cases h20 : j.val = 20
  · rw [slotP 6 (by omega) (Fin.ext (by simp [t4P, t4W, h20])), adc_lt _ _ j.val hj (by omega)]
    have e : (⟨6, by omega⟩ : Fin (LNS 0 + 2 + LNR)) = sTape (sk 0 5) := Fin.ext (by simp [sTape, sk])
    rw [e, o5]
    simp [PrimThrW.Nums3.nums3InPorts, h20]
  rw [install_other _ _ _ _ (fun j' => t4P_ne_t4W_small alg j' j h0 h1 h2 h20)]
  by_cases hs : j.val < 20
  · have ew : t4W alg j = ⟨TS + (j.val - 3), by omega⟩ := Fin.ext (by simp [t4W, h0, h1, h2, h20, hs])
    rw [ew, amb0_ge alg w n L W _ _ (by omega), adc_lt _ _ j.val hj (by omega)]
    simp [PrimThrW.Nums3.nums3InPorts, PrimThrW.NumsP.numsInPorts, hs, h0, h1, h2]
  · have ew : t4W alg j = ⟨TS + (17 + (j.val - 21)), by unfold t4b at hb; omega⟩ :=
      Fin.ext (by simp [t4W, h0, h1, h2, h20, hs])
    rw [ew, amb0_ge alg w n L W _ _ (by omega), adc_ge _ _ j.val hj (by omega)]

/-- The tapes after W6. -/
noncomputable def amb2 (w : List Bool) (n L W : ℕ) (out0 : Fin (LNS 0 + 2 + LNR + 1) → List Bool)
    (outW : Fin (21 + (W6.TI alg + 1)) → List Bool) : Fin (TS + t4X alg) → List Bool :=
  install (t4W alg) (amb1 alg w n L W out0) outW

/-- **The first three phases' input**: the stage's own tapes are its entry bank again. -/
theorem matchA (w : List Bool) (n L W : ℕ) (tout0 : Fin (LNS 0 + 2 + LNR) → List Bool) (m0 : ℕ)
    (o0 : tout0 (sTape (sk 0 0)) = RepairOrdinary.frame w) (o1 : tout0 (sTape (sk 0 1)) = List.replicate W true)
    (outW : Fin (21 + (W6.TI alg + 1)) → List Bool) (oW : outW ⟨0, by omega⟩ = RepairOrdinary.frame w)
    (i : Fin TS) :
    amb2 alg w n L W (Fin.addCases tout0 (fun _ : Fin 1 => List.replicate m0 false)) outW (t4E alg i) =
      rawIn w n L W i := by
  have hi := i.isLt
  have e1 := LNS0_val; have e2 := LNR_val; have e3 := TS_val; have e4 := TI_w6x alg
  have hb := t4X_ge alg
  unfold amb2
  by_cases h0 : i.val = 0
  · have e : t4E alg i = t4W alg ⟨0, by omega⟩ := Fin.ext (by simp [t4E, t4W, h0])
    rw [e, install_slot _ (t4W_inj alg), oW, rawIn_val]
    simp [h0]
  rw [install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e
    simp only [t4E, t4W] at hv
    split_ifs at hv <;> omega)]
  unfold amb1
  by_cases h4 : i.val = 4
  · have e : t4E alg i = t4P alg ⟨2, by omega⟩ := Fin.ext (by simp [t4E, t4P, h4])
    rw [e, install_slot _ (t4P_inj alg), adc_lt _ _ 2 (by omega) (by omega)]
    have e' : (⟨2, by omega⟩ : Fin (LNS 0 + 2 + LNR)) = sTape (sk 0 1) := Fin.ext (by simp [sTape, sk])
    rw [e', o1, rawIn_val]
    simp [h4]
  rw [install_other _ _ _ _ (fun j e => by
    have hv := congrArg Fin.val e
    simp only [t4E, t4P] at hv
    have := j.isLt
    split_ifs at hv <;> omega)]
  have e : t4E alg i = ⟨i.val, by omega⟩ := rfl
  rw [e, amb0_lt alg w n L W i.val _ hi]

end NearCubicWires.WireExponent3_5.PrimT.TS4
