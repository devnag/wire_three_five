import Proof.Wire_3_5.Primitive.Writers.GeoFront

/-! # C3 request writer, part 4: the docked stages, generic in the slot map

The C3 writer's machine docks base and component machines into one bank by injective slot maps: the writers' runs
(`WriterIfaceJ.WriterRun`, ports on two given tapes, every other tape in a fresh region), C2's `Unframe`, base
`CapReader` and `UnaryCalc`, and the fill count's append program (`appP`: the count `1^W` extended by `k` ones per
one of each unary input `1^h`, `1^{Q'}`, `1^m`, `1^{pr}`, so the registers' capacity covers the request's numbers).

Paper quantity: none (the machine plumbing of alg:compiler's request writer, P3:1886-1906). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace NearCubicWires.WireExponent3_5.PrimAsm.C3Dock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound NearCubicWires.BlockPlatform NearCubicWires.WireExponent3_5
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.ListMachine NearCubicWires.WireExponent3_5.ListMachine.Row
open NearCubicWires.WireExponent3_5.PrimAsm NearCubicWires.WireExponent3_5.PrimAsm.GeoFront
open NearCubicWires.RepairOrdinary.StablePartition.Workspace (overlay)

/-! ## Writers -/

theorem readyStep {t s : ℕ} {p : Machine t s} {b : ℕ} {inp out : Fin t → List Bool}
    (h : ClockJoin.ReadyRun p b inp out) : Step p b (fun _ => 0) inp (fun _ => 0) out := by
  obtain ⟨r, hr, ht, hh, _⟩ := h
  exact Step.of_run hr (funext hh) ht

/-- A writer's slots: the input port at `a`, the output port at `b`, every other tape `j` at `base + j`. -/
def portSl {t u : ℕ} (i o : Fin t) (a b : Fin u) (base : ℕ) (hb : base + t ≤ u) : Fin t → Fin u :=
  fun j => if j = i then a else if j = o then b else ⟨base + j.val, by omega⟩

theorem portSl_i {t u : ℕ} (i o : Fin t) (a b : Fin u) (base : ℕ) (hb : base + t ≤ u) :
    portSl i o a b base hb i = a := by simp [portSl]

theorem portSl_o {t u : ℕ} (i o : Fin t) (hio : i ≠ o) (a b : Fin u) (base : ℕ) (hb : base + t ≤ u) :
    portSl i o a b base hb o = b := by simp [portSl, Ne.symm hio]

theorem portSl_val {t u : ℕ} (i o : Fin t) (a b : Fin u) (base : ℕ) (hb : base + t ≤ u) (j : Fin t)
    (h1 : j ≠ i) (h2 : j ≠ o) : (portSl i o a b base hb j).val = base + j.val := by simp [portSl, h1, h2]

theorem portSl_inj {t u : ℕ} (i o : Fin t) (hio : i ≠ o) (a b : Fin u) (hab : a ≠ b) (base : ℕ)
    (hb : base + t ≤ u) (ha : a.val < base) (hb' : b.val < base) : Function.Injective (portSl i o a b base hb) := by
  intro x y hxy
  by_cases xi : x = i
  · by_cases yi : y = i
    · rw [xi, yi]
    · by_cases yo : y = o
      · rw [xi, yo, portSl_i, portSl_o _ _ hio] at hxy; exact absurd hxy hab
      · have e := congrArg Fin.val hxy
        rw [xi, portSl_i, portSl_val _ _ _ _ _ _ _ yi yo] at e; omega
  · by_cases xo : x = o
    · by_cases yi : y = i
      · rw [xo, yi, portSl_i, portSl_o _ _ hio] at hxy; exact absurd hxy.symm hab
      · by_cases yo : y = o
        · rw [xo, yo]
        · have e := congrArg Fin.val hxy
          rw [xo, portSl_o _ _ hio, portSl_val _ _ _ _ _ _ _ yi yo] at e; omega
    · by_cases yi : y = i
      · have e := congrArg Fin.val hxy
        rw [yi, portSl_i, portSl_val _ _ _ _ _ _ _ xi xo] at e; omega
      · by_cases yo : y = o
        · have e := congrArg Fin.val hxy
          rw [yo, portSl_o _ _ hio, portSl_val _ _ _ _ _ _ _ xi xo] at e; omega
        · have e := congrArg Fin.val hxy
          rw [portSl_val _ _ _ _ _ _ _ xi xo, portSl_val _ _ _ _ _ _ _ yi yo] at e
          exact Fin.ext (by omega)

theorem portSl_ne {t u : ℕ} (i o : Fin t) (a b : Fin u) (base : ℕ) (hb : base + t ≤ u) (x : Fin u) (hxa : x ≠ a)
    (hxb : x ≠ b) (hx : x.val < base ∨ base + t ≤ x.val) : ∀ j, portSl i o a b base hb j ≠ x := by
  intro j e
  by_cases h1 : j = i
  · rw [h1, portSl_i] at e; exact hxa e.symm
  · by_cases h2 : j = o
    · rw [h2] at e
      by_cases h3 : o = i
      · rw [h3, portSl_i] at e; exact hxa e.symm
      · rw [portSl_o _ _ (Ne.symm h3)] at e; exact hxb e.symm
    · have e' := congrArg Fin.val e
      rw [portSl_val _ _ _ _ _ _ _ h1 h2] at e'
      have := j.isLt
      omega

/-- **A writer's run, docked** at the ports `a` (the request) and `b` (the output), its other tapes in the fresh
region `[base, base + t)`: `frame w` kept, `v` written, every tape off the slots unchanged, the heads kept. -/
theorem wdock {t s u : ℕ} {M : Machine t s} {B : ℕ} {i o : Fin t} {w v : List Bool} (hio : i ≠ o)
    (h : WriterIfaceJ.WriterRun M B i o w v) (a b : Fin u) (hab : a ≠ b) (base : ℕ) (hb : base + t ≤ u)
    (ha : a.val < base) (hb' : b.val < base) (H : Fin u → ℕ) (A : Fin u → List Bool)
    (hHa : H a = 0) (hHb : H b = 0) (hHr : ∀ x : Fin u, base ≤ x.val → x.val < base + t → H x = 0)
    (hAa : A a = frame w) (hAb : A b = []) (hAr : ∀ x : Fin u, base ≤ x.val → x.val < base + t → A x = []) :
    ∃ A' : Fin u → List Bool, Step (RecoveryFocus.machine (portSl i o a b base hb) M) B H A H A' ∧
      A' a = frame w ∧ A' b = v ∧
      (∀ x : Fin u, x ≠ a → x ≠ b → (x.val < base ∨ base + t ≤ x.val) → A' x = A x) := by
  obtain ⟨J, _, hr⟩ := h
  have hs := readyStep hr
  have hinj := portSl_inj i o hio a b hab base hb ha hb'
  have hreg : ∀ j : Fin t, j ≠ i → j ≠ o → base ≤ (portSl i o a b base hb j).val ∧
      (portSl i o a b base hb j).val < base + t := by
    intro j h1 h2
    rw [portSl_val _ _ _ _ _ _ _ h1 h2]
    have := j.isLt
    omega
  have d := dockZ hs (portSl i o a b base hb) hinj H A
    (by
      intro j
      by_cases h1 : j = i
      · rw [h1, portSl_i]; exact hHa
      · by_cases h2 : j = o
        · rw [h2, portSl_o _ _ hio]; exact hHb
        · exact hHr _ (hreg j h1 h2).1 (hreg j h1 h2).2)
    (by
      intro j
      by_cases h1 : j = i
      · rw [h1, portSl_i, hAa]; simp [WriterIface.inBank]
      · by_cases h2 : j = o
        · rw [h2, portSl_o _ _ hio, hAb]; simp [WriterIface.inBank, Ne.symm hio]
        · rw [hAr _ (hreg j h1 h2).1 (hreg j h1 h2).2]; simp [WriterIface.inBank, h1])
  refine ⟨_, d, ?_, ?_, fun x h1 h2 h3 => install_other _ _ _ _ (portSl_ne i o a b base hb x h1 h2 h3)⟩
  · have e := install_slot (portSl i o a b base hb) hinj A (WriterIfaceJ.outBankJ i o w v J) i
    rw [portSl_i] at e
    rw [e]
    exact WriterIfaceJ.outBankJ_in i o w v J
  · have e := install_slot (portSl i o a b base hb) hinj A (WriterIfaceJ.outBankJ i o w v J) o
    rw [portSl_o _ _ hio] at e
    rw [e]
    exact WriterIfaceJ.outBankJ_out i o hio w v J

/-! ## The front's machines -/

/-- The unframing machine (C2's `Unframe` under the masked reset). -/
noncomputable def unM := MaskedReset.machine Unframe.machine (fun _ => true)

/-- **The raw request, docked**: from `frame w` on slot `0` and blank slots `1`, `2`, the raw word `w` on slot `1`. -/
theorem un_dock {u : ℕ} (sl : Fin 3 → Fin u) (hsl : Function.Injective sl) (w : List Bool) (H : Fin u → ℕ)
    (hH : ∀ j, H (sl j) = 0) (B : Fin u → List Bool) (h0 : B (sl 0) = frame w) (h1 : B (sl 1) = [])
    (h2 : B (sl 2) = []) :
    ∃ B' : Fin u → List Bool,
      Step (RecoveryFocus.machine sl unM) (2 * (2 * w.length + 1) + 2) H B H B' ∧
      B' (sl 0) = frame w ∧ B' (sl 1) = w ∧ (∀ i, (∀ j, sl j ≠ i) → B' i = B i) := by
  obtain ⟨m1, h⟩ := maskBlank (Unframe.run [] w [] [] []) (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have h' := Step.congr (hout' := fun _ => 0) (Step.congr_in (hin' := fun _ => 0) h (by
      funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i
      · fin_cases a <;> rfl
      · simp) rfl) (by
      funext i; refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp) rfl
  have d := dockZ h' sl hsl H B hH
    (by
      intro j
      fin_cases j
      · change B (sl 0) = [] ++ frame w ++ []
        simp [h0]
      · change B (sl 1) = overlay [] []
        simp [h1, overlay_nil]
      · change B (sl 2) = List.replicate 0 false
        simp [h2])
  refine ⟨_, d, ?_, ?_, fun i hi => install_other _ _ _ _ hi⟩
  · rw [install_slot _ hsl]
    simp
    rfl
  · rw [install_slot _ hsl]
    simp [overlay_nil]
    rfl

/-- The capacity reader (base `CapReader` under the masked reset). -/
noncomputable def crM := MaskedReset.machine PCJ45bee56da9f34d5a_CapReader.machine (fun _ => true)

/-- The capacity reader's step bound. -/
def crCost (v : ℕ) : ℕ := 2 * (8 * v + 20 * natBitLength v + 17) + 2

/-- **`1^v`, docked**: from `natWord v ++ sfx` on slot `0` and blank slots `1 … 11`, `1^v` on slots `8` and `9`. -/
theorem cr_dock {u : ℕ} (sl : Fin 12 → Fin u) (hsl : Function.Injective sl) (v : ℕ) (sfx : List Bool)
    (H : Fin u → ℕ) (hH : ∀ j, H (sl j) = 0) (B : Fin u → List Bool)
    (h0 : B (sl 0) = RepairRepresentation.natWord v ++ sfx) (hz : ∀ j : Fin 12, j ≠ 0 → B (sl j) = []) :
    ∃ B' : Fin u → List Bool,
      Step (RecoveryFocus.machine sl crM) (crCost v) H B H B' ∧
      B' (sl 0) = RepairRepresentation.natWord v ++ sfx ∧ B' (sl 8) = List.replicate v true ∧
      B' (sl 9) = List.replicate v true ∧ (∀ i, (∀ j, sl j ≠ i) → B' i = B i) := by
  obtain ⟨H0, A, h, hout⟩ := PCJ45bee56da9f34d5a_CapReader.natural_run [] sfx v
  obtain ⟨h0', _, h8, _, h9, _, _, _⟩ := hout
  obtain ⟨m2, hm⟩ := maskBlank h (fun _ => true) (by intro i _; fin_cases i <;> rfl) 0
  have eh0 : (Fin.addCases (PCJ45bee56da9f34d5a_CapReader.initialHeads ([] : List Bool).length) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i
    · fin_cases a <;> rfl
    · simp
  have eh1 : (Fin.addCases (fun i => if (fun _ => true) i = true then 0 else H0 i) (fun _ : Fin 1 => 0) :
      Fin (11 + 1) → ℕ) = fun _ => 0 := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun u => ?_) i <;> simp
  have hm' := (hm.congr_in eh0 rfl).congr eh1 rfl
  have d := dockZ hm' sl hsl H B hH (by
    intro j
    fin_cases j
    · show B (sl 0) = _
      rw [h0]; rfl
    all_goals first
      | (show B (sl _) = _; rw [hz _ (by decide)]; rfl))
  refine ⟨_, d, ?_, ?_, ?_, fun i hi => install_other _ _ _ _ hi⟩
  · have e := install_slot sl hsl B (Fin.addCases (motive := fun _ => List Bool) A (fun _ : Fin 1 => List.replicate m2 false)) 0
    rw [e]
    exact h0'
  · have e := install_slot sl hsl B (Fin.addCases (motive := fun _ => List Bool) A (fun _ : Fin 1 => List.replicate m2 false)) 8
    rw [e]
    exact h8
  · have e := install_slot sl hsl B (Fin.addCases (motive := fun _ => List Bool) A (fun _ : Fin 1 => List.replicate m2 false)) 9
    rw [e]
    exact h9

/-- **`1^{C(n+1)^D}`, docked** (base `UnaryCalc.poly_step`): from `1^n` on the input slot and blank slots. -/
theorem uc_dock {u : ℕ} (D C n : ℕ) (sl : Fin (UnaryCalc.tapes D) → Fin u) (hsl : Function.Injective sl)
    (H : Fin u → ℕ) (hH : ∀ j, H (sl j) = 0) (B : Fin u → List Bool)
    (hin : B (sl (UnaryCalc.inputTape D)) = List.replicate n true)
    (hz : ∀ k, k ≠ UnaryCalc.inputTape D → B (sl k) = []) :
    ∃ B' : Fin u → List Bool,
      Step (RecoveryFocus.machine sl (PCPSerializerCapacity.Power.machine D C))
        (PCPSerializerCapacity.Power.budget D C n) H B H B' ∧
      B' (sl (UnaryCalc.outputTape D)) = List.replicate (UnaryCalc.value D C n) true ∧
      B' (sl (UnaryCalc.inputTape D)) = List.replicate n true ∧ (∀ i, (∀ j, sl j ≠ i) → B' i = B i) := by
  obtain ⟨out, h, hi, ho⟩ := UnaryCalc.poly_step D C n
  have d := dockZ h sl hsl H B hH (by
    intro k
    by_cases hk : k = UnaryCalc.inputTape D
    · subst hk
      rw [hin]
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, UnaryCalc.inputTape]
    · rw [hz k hk]
      have hv : k.val ≠ 0 := fun e => hk (Fin.ext e)
      simp [RepairSource.ProjectionNormalization.DimensionPolynomial.input, hv])
  refine ⟨_, d, ?_, ?_, fun i hi => install_other _ _ _ _ hi⟩
  · rw [install_slot _ hsl]; exact ho
  · rw [install_slot _ hsl]; exact hi

end NearCubicWires.WireExponent3_5.PrimAsm.C3Dock
