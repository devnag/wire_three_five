import Proof.Wire_3_5.UnionMachine.CWParPre

/-! # C6 front, U5, the code writers: the parity writer's suffix — the circuit code

A normalized circuit's code is the tagged list `[encodeNat tag, encodeNat k, bottoms, top]` (base's
`encodeNormalizedSymmetricThresholdCircuit` / `encodeNormalizedThresholdThresholdCircuit`), i.e.
`cons tag (cons kc (cons BL (cons TOP 0)))`. From the bottoms' codes (the loop's accumulator), the counter at `k`, the
top's code and the tag's code (both framed), this machine (`sufM`, 571 tapes) writes the circuit code's `natWord`:
* base's serializer on the accumulator (`BL`) and on the counter's fields (`encodeNat k`), each copied exact;
* four tagged cons, each copied exact; FP's `natWord` writer on the output tape `6`.

Paper quantity of the main type (**`suf_step`**): the code of the encoding parity atom, as the writer outputs it. -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.UnionMachine.CWParSuf
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.RepairRepresentation
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.UnionMachine.CWParCnt NearCubicWires.WireExponent3_5.UnionMachine.CWParStages
open NearCubicWires.WireExponent3_5.UnionMachine.CWParRound (cons gsOf code_gsOf sgl_gsOf)
open NearCubicWires.WireExponent3_5.UnionMachine.CWWords (natW natCost natIn natIn_val natStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWCore (serM serIn serCost serStage)
open NearCubicWires.WireExponent3_5.UnionMachine.CWMain (serIn_val)
open NearCubicWires.WireExponent3_5.UnionMachine (FrontLoopKit.step_of_ready FrontKit.ready_of_step)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.RepairSource.VerifierDecoding (CompareMachine.word)

/-- **The circuit code** from the bottoms' codes, the bottom count, the top's code and the tag's code. -/
def sufCode (accL : List (List Bool)) (k topv tagv : ℕ) : ℕ :=
  cons tagv (cons (CanonicalBinary.encodeNat k) (cons (PCPTraversal.code accL) (cons topv 0)))

/-! ## The layout -/

def ser1Sl (j : Fin 129) : Fin 571 :=
  ⟨if j.val = 0 then 0 else if j.val = 2 then 1 else if j.val = 1 then 8 else j.val + 6, by split_ifs <;> omega⟩
def cp1Sl : Fin 4 → Fin 571 := ![83, 7, 135, 136]
def ser2Sl (j : Fin 129) : Fin 571 :=
  ⟨if j.val = 0 then 2 else if j.val = 2 then 3 else if j.val = 1 then 137 else j.val + 135, by split_ifs <;> omega⟩
def cp2Sl : Fin 4 → Fin 571 := ![212, 7, 264, 265]
def zSl : Fin 1 → Fin 571 := fun _ => 266
/-- The tagged cons on its operands `a` (tape 2), `r` (tape 3), with fresh tapes from `base`. -/
def cSl (a r base : ℕ) (ha : a < 571) (hr : r < 571) (hb : base + 74 < 571) (j : Fin 76) : Fin 571 :=
  ⟨if j.val = 2 then a else if j.val = 3 then r else if j.val < 2 then j.val + base else j.val + base - 2,
    by split_ifs <;> omega⟩
def c1Sl : Fin 76 → Fin 571 := cSl 4 266 267 (by decide) (by decide) (by decide)
def cp3Sl : Fin 4 → Fin 571 := ![329, 7, 341, 342]
def c2Sl : Fin 76 → Fin 571 := cSl 135 341 343 (by decide) (by decide) (by decide)
def cp4Sl : Fin 4 → Fin 571 := ![405, 7, 417, 418]
def c3Sl : Fin 76 → Fin 571 := cSl 264 417 419 (by decide) (by decide) (by decide)
def cp5Sl : Fin 4 → Fin 571 := ![481, 7, 493, 494]
def c4Sl : Fin 76 → Fin 571 := cSl 5 493 495 (by decide) (by decide) (by decide)
def natSl : Fin 5 → Fin 571 := ![557, 7, 6, 569, 570]

theorem cSl_inj (a r base : ℕ) (ha : a < 571) (hr : r < 571) (hb : base + 74 < 571) (hra : a ≠ r)
    (hlo : a < base ∧ r < base ∨ False) : Function.Injective (cSl a r base ha hr hb) := by
  intro x y h; have hv := congrArg Fin.val h; simp only [cSl] at hv
  have := x.isLt; have := y.isLt
  rcases hlo with ⟨h1, h2⟩ | h
  · apply Fin.ext; split_ifs at hv <;> omega
  · exact h.elim

theorem cSl_val (a r base : ℕ) (ha : a < 571) (hr : r < 571) (hb : base + 74 < 571) (j : Fin 76) :
    (cSl a r base ha hr hb j).val =
      if j.val = 2 then a else if j.val = 3 then r else if j.val < 2 then j.val + base else j.val + base - 2 := rfl

theorem cp1Sl_inj : Function.Injective cp1Sl := by decide
theorem cp2Sl_inj : Function.Injective cp2Sl := by decide
theorem cp3Sl_inj : Function.Injective cp3Sl := by decide
theorem cp4Sl_inj : Function.Injective cp4Sl := by decide
theorem cp5Sl_inj : Function.Injective cp5Sl := by decide
theorem natSl_inj : Function.Injective natSl := by decide
theorem zSl_inj : Function.Injective zSl := fun a b _ => Subsingleton.elim a b
theorem ser1Sl_inj : Function.Injective ser1Sl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ser1Sl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem ser2Sl_inj : Function.Injective ser2Sl := by
  intro a b h; have hv := congrArg Fin.val h; simp only [ser2Sl] at hv; apply Fin.ext; split_ifs at hv <;> omega
theorem c1Sl_inj : Function.Injective c1Sl := cSl_inj _ _ _ _ _ _ (by decide) (Or.inl ⟨by decide, by decide⟩)
theorem c2Sl_inj : Function.Injective c2Sl := cSl_inj _ _ _ _ _ _ (by decide) (Or.inl ⟨by decide, by decide⟩)
theorem c3Sl_inj : Function.Injective c3Sl := cSl_inj _ _ _ _ _ _ (by decide) (Or.inl ⟨by decide, by decide⟩)
theorem c4Sl_inj : Function.Injective c4Sl := cSl_inj _ _ _ _ _ _ (by decide) (Or.inl ⟨by decide, by decide⟩)

theorem cp1Sl_val (j : Fin 4) : (cp1Sl j).val = [83, 7, 135, 136].getD j.val 0 := by fin_cases j <;> rfl
theorem cp2Sl_val (j : Fin 4) : (cp2Sl j).val = [212, 7, 264, 265].getD j.val 0 := by fin_cases j <;> rfl
theorem cp3Sl_val (j : Fin 4) : (cp3Sl j).val = [329, 7, 341, 342].getD j.val 0 := by fin_cases j <;> rfl
theorem cp4Sl_val (j : Fin 4) : (cp4Sl j).val = [405, 7, 417, 418].getD j.val 0 := by fin_cases j <;> rfl
theorem cp5Sl_val (j : Fin 4) : (cp5Sl j).val = [481, 7, 493, 494].getD j.val 0 := by fin_cases j <;> rfl

noncomputable def cellR := RecoveryFocus.machine (fun _ : Fin 1 => (7 : Fin 571)) NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def ser1R := RecoveryFocus.machine ser1Sl serM
noncomputable def cp1R := RecoveryFocus.machine cp1Sl (Rewind.machine cpW.toProg.compile)
noncomputable def ser2R := RecoveryFocus.machine ser2Sl serM
noncomputable def cp2R := RecoveryFocus.machine cp2Sl (Rewind.machine cpW.toProg.compile)
noncomputable def zR := RecoveryFocus.machine zSl NearCubicWires.WireExponent3_5.PrimT.cellM
noncomputable def c1R := RecoveryFocus.machine c1Sl PCPPRequestTaggedCons.machine
noncomputable def cp3R := RecoveryFocus.machine cp3Sl (Rewind.machine cpW.toProg.compile)
noncomputable def c2R := RecoveryFocus.machine c2Sl PCPPRequestTaggedCons.machine
noncomputable def cp4R := RecoveryFocus.machine cp4Sl (Rewind.machine cpW.toProg.compile)
noncomputable def c3R := RecoveryFocus.machine c3Sl PCPPRequestTaggedCons.machine
noncomputable def cp5R := RecoveryFocus.machine cp5Sl (Rewind.machine cpW.toProg.compile)
noncomputable def c4R := RecoveryFocus.machine c4Sl PCPPRequestTaggedCons.machine
noncomputable def natR := RecoveryFocus.machine natSl (Rewind.machine natW.toProg.compile)

/-- **The parity writer's suffix machine.** -/
noncomputable def sufM :=
  Composition.machine cellR (Composition.machine ser1R (Composition.machine cp1R (Composition.machine ser2R
    (Composition.machine cp2R (Composition.machine zR (Composition.machine c1R (Composition.machine cp3R
      (Composition.machine c2R (Composition.machine cp4R (Composition.machine c3R (Composition.machine cp5R
        (Composition.machine c4R natR))))))))))))

/-- The suffix's entry: the accumulator, the count `k`, the counter and its count, the top's and the tag's codes. -/
def sufIn (A K C N T G : List Bool) : Fin 571 → List Bool :=
  fun t => if t.val = 0 then A else if t.val = 1 then K else if t.val = 2 then C else if t.val = 3 then N
    else if t.val = 4 then T else if t.val = 5 then G else []

theorem zeroH (t : ℕ) (sl : Fin t → Fin 571) : dockH sl (fun _ => 0) (fun _ => 0) = fun _ => 0 :=
  dockH_existing sl _ _ (fun _ => rfl)

/-- The suffix's fuel. -/
noncomputable def sufCost (accL : List (List Bool)) (k topv tagv : ℕ) : ℕ :=
  1 + 1 + (serCost accL + 1 + ((2 * (14 * (PCPTraversal.code accL).bits.length + 5) + 2) + 1 + (serCost (gsOf k) + 1 + (
    (2 * (14 * (CanonicalBinary.encodeNat k).bits.length + 5) + 2) + 1 + (1 + 1 + (
    PCPPRequestTaggedCons.budget topv 0 + 1 + ((2 * (14 * (cons topv 0).bits.length + 5) + 2) + 1 + (
    PCPPRequestTaggedCons.budget (PCPTraversal.code accL) (cons topv 0) + 1 + (
    (2 * (14 * (cons (PCPTraversal.code accL) (cons topv 0)).bits.length + 5) + 2) + 1 + (
    PCPPRequestTaggedCons.budget (CanonicalBinary.encodeNat k) (cons (PCPTraversal.code accL) (cons topv 0)) + 1 + (
    (2 * (14 * (cons (CanonicalBinary.encodeNat k) (cons (PCPTraversal.code accL) (cons topv 0))).bits.length + 5) + 2) + 1 + (
    PCPPRequestTaggedCons.budget tagv (cons (CanonicalBinary.encodeNat k) (cons (PCPTraversal.code accL) (cons topv 0))) + 1 + (
    (2 * natCost (sufCode accL k topv tagv) + 2))))))))))))))

/-- A tagged cons docked on a bank: its operands framed on `a` and `r`, fresh tapes from `base`. -/
theorem cons_dock (a r base : ℕ) (ha : a < 571) (hr : r < 571) (hb : base + 74 < 571) (hra : a ≠ r)
    (hlo : a < base ∧ r < base) (x y : ℕ) (B : Fin 571 → List Bool) (hA : B ⟨a, ha⟩ = frame x.bits)
    (hR : B ⟨r, hr⟩ = frame y.bits) (hF : ∀ t : Fin 571, base ≤ t.val → t.val < base + 74 → B t = []) :
    ∃ o : Fin 76 → List Bool, Step (RecoveryFocus.machine (cSl a r base ha hr hb) PCPPRequestTaggedCons.machine)
      (PCPPRequestTaggedCons.budget x y) (fun _ => 0) B (fun _ => 0) (install (cSl a r base ha hr hb) B o) ∧
      ∃ pd, o 64 = frame (cons x y).bits ++ List.replicate pd false := by
  obtain ⟨o, r9, ⟨pd, q64⟩, -⟩ := PCPPRequestTaggedCons.cons_run x y
  have d := (FrontLoopKit.step_of_ready r9).dock (cSl a r base ha hr hb)
    (cSl_inj a r base ha hr hb hra (Or.inl hlo)) (fun _ => 0) B (fun _ => rfl) (by
    intro k
    show B (cSl a r base ha hr hb k) = PCPPRequestTaggedCons.input x y k
    unfold PCPPRequestTaggedCons.input PCPPRequestPair.input PCPPairCanonical.input
    by_cases h2 : k.val = 2
    · rw [dif_pos (by omega)]; simp only [h2, if_true]
      rw [show cSl a r base ha hr hb k = ⟨a, ha⟩ from Fin.ext (by simp [cSl, h2]), hA]
    · by_cases h3 : k.val = 3
      · rw [dif_pos (by omega)]; simp only [h3, if_true, show (3 : ℕ) ≠ 2 by decide, if_false]
        rw [show cSl a r base ha hr hb k = ⟨r, hr⟩ from Fin.ext (by simp [cSl, h3]), hR]
      · have hk := k.isLt
        rw [hF _ (by simp only [cSl]; split_ifs <;> omega) (by simp only [cSl]; split_ifs <;> omega)]
        split_ifs <;> simp_all)
  rw [zeroH] at d
  exact ⟨o, d, pd, q64⟩

/-- A copy docked on a bank. -/
theorem cp_dock (sl : Fin 4 → Fin 571) (hsl : Function.Injective sl) (y rest : List Bool) (B : Fin 571 → List Bool)
    (h0 : B (sl 0) = frame y ++ rest) (h1 : B (sl 1) = [false]) (h2 : B (sl 2) = []) (h3 : B (sl 3) = []) :
    ∃ o : Fin 4 → List Bool, Step (RecoveryFocus.machine sl (Rewind.machine cpW.toProg.compile))
      (2 * (14 * y.length + 5) + 2) (fun _ => 0) B (fun _ => 0) (install sl B o) ∧
      o 0 = frame y ++ rest ∧ o 1 = [false] ∧ o 2 = frame y := by
  obtain ⟨o, s, c0, c1, c2⟩ := cpStage y rest
  have d := s.dock sl hsl (fun _ => 0) B (fun _ => rfl) (by
    intro k; rw [cpIn_val]
    fin_cases k
    · exact h0
    · exact h1
    · exact h2
    · exact h3)
  rw [zeroH] at d
  exact ⟨o, d, c0, c1, c2⟩

/-- **The parity writer's suffix**: the circuit code's `natWord` on the output tape `6`. -/
theorem suf_step (accL : List (List Bool)) (k topv tagv : ℕ) (hk : accL.length = k) :
    ∃ out : Fin 571 → List Bool,
      Step sufM (sufCost accL k topv tagv) (fun _ => 0)
        (sufIn (accL.flatMap frame) (CompareMachine.word k) (sgl k.bits) (CompareMachine.word k.bits.length)
          (frame topv.bits) (frame tagv.bits)) (fun _ => 0) out ∧
      out 6 = frame (natWord (sufCode accL k topv tagv)) := by
  set BL := PCPTraversal.code accL with hBL
  set KC := CanonicalBinary.encodeNat k with hKC
  set B0 := sufIn (accL.flatMap frame) (CompareMachine.word k) (sgl k.bits) (CompareMachine.word k.bits.length)
    (frame topv.bits) (frame tagv.bits) with hB0
  have f0 : ∀ t : Fin 571, 6 ≤ t.val → B0 t = [] := by
    intro t ht; simp only [hB0, sufIn]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  -- 1: the cell
  have d1 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock (fun _ : Fin 1 => (7 : Fin 571))
    (fun a b _ => Subsingleton.elim a b) (fun _ => 0) B0 (fun _ => rfl) (fun _ => f0 7 (by decide))
  rw [zeroH] at d1
  set B1 := install (fun _ : Fin 1 => (7 : Fin 571)) B0 (fun _ => [false]) with hB1
  have b1 : ∀ t : Fin 571, t.val ≠ 7 → B1 t = B0 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have b17 : B1 7 = [false] := install_slot (fun _ : Fin 1 => (7 : Fin 571)) (fun a b _ => Subsingleton.elim a b) _ _ 0
  have f1 : ∀ t : Fin 571, 8 ≤ t.val → B1 t = [] := fun t ht => by rw [b1 _ (by omega), f0 _ (by omega)]
  -- 2: the bottoms' list
  obtain ⟨o2, s2, z0, z2, z77⟩ := serStage accL
  have d2 := s2.dock ser1Sl ser1Sl_inj (fun _ => 0) B1 (fun _ => rfl) (by
    intro j; rw [serIn_val]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show ser1Sl j = (0 : Fin 571) from Fin.ext (by simp [ser1Sl, h0]), b1 _ (by decide)]
      simp [hB0, sufIn]
    · rw [if_neg h0]
      by_cases h2 : j.val = 2
      · rw [if_pos h2, show ser1Sl j = (1 : Fin 571) from Fin.ext (by simp [ser1Sl, h2]), b1 _ (by decide), hk]
        simp [hB0, sufIn]
      · have hj := j.isLt
        rw [if_neg h2, f1 _ (by simp only [ser1Sl]; split_ifs <;> omega)])
  rw [zeroH] at d2
  set B2 := install ser1Sl B1 o2 with hB2
  have b2h : ∀ j, B2 (ser1Sl j) = o2 j := fun j => install_slot _ ser1Sl_inj _ _ _
  have b2 : ∀ t : Fin 571, ((2 ≤ t.val ∧ t.val < 8) ∨ 135 ≤ t.val) → B2 t = B1 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [ser1Sl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have f2 : ∀ t : Fin 571, 135 ≤ t.val → B2 t = [] := fun t ht => by rw [b2 _ (by omega), f1 _ (by omega)]
  -- 3: copy it exact
  obtain ⟨o3, d3, -, k1, k2⟩ := cp_dock cp1Sl cp1Sl_inj BL.bits (List.replicate
    (PCPPairReusable.capacity (PCPSerializerMass.mass accL) - (frame BL.bits).length) false) B2
    (by show B2 83 = _; rw [show (83 : Fin 571) = ser1Sl 77 from rfl, b2h, z77]; rfl)
    (by show B2 7 = _; rw [b2 _ (by decide), b17])
    (by show B2 135 = _; rw [f2 _ (by decide)])
    (by show B2 136 = _; rw [f2 _ (by decide)])
  set B3 := install cp1Sl B2 o3 with hB3
  have b3h : ∀ j, B3 (cp1Sl j) = o3 j := fun j => install_slot _ cp1Sl_inj _ _ _
  have b3 : ∀ t : Fin 571, (∀ j, (cp1Sl j).val ≠ t.val) → B3 t = B2 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f3 : ∀ t : Fin 571, 137 ≤ t.val → B3 t = [] := fun t ht => by
    rw [b3 _ (by intro j; rw [cp1Sl_val]; fin_cases j <;> simp <;> omega), f2 _ (by omega)]
  have h37 : B3 7 = [false] := by rw [show (7 : Fin 571) = cp1Sl 1 from rfl, b3h, k1]
  have h3BL : B3 135 = frame BL.bits := by rw [show (135 : Fin 571) = cp1Sl 2 from rfl, b3h, k2]
  have keep3 : ∀ t : Fin 571, 2 ≤ t.val → t.val < 7 → B3 t = B0 t := fun t h1 h2 => by
    rw [b3 _ (by intro j; rw [cp1Sl_val]; fin_cases j <;> simp <;> omega), b2 _ (by omega), b1 _ (by omega)]
  -- 4: the bottom count's code
  obtain ⟨o4, s4, y0, y2, y77⟩ := serStage (gsOf k)
  have d4 := s4.dock ser2Sl ser2Sl_inj (fun _ => 0) B3 (fun _ => rfl) (by
    intro j; rw [serIn_val]
    by_cases h0 : j.val = 0
    · rw [if_pos h0, show ser2Sl j = (2 : Fin 571) from Fin.ext (by simp [ser2Sl, h0]), keep3 _ (by decide) (by decide)]
      simp [hB0, sufIn, sgl_gsOf]
    · rw [if_neg h0]
      by_cases h2 : j.val = 2
      · rw [if_pos h2, show ser2Sl j = (3 : Fin 571) from Fin.ext (by simp [ser2Sl, h2]),
          keep3 _ (by decide) (by decide)]
        simp [hB0, sufIn, gsOf]
      · have hj := j.isLt
        rw [if_neg h2, f3 _ (by simp only [ser2Sl]; split_ifs <;> omega)])
  rw [zeroH] at d4
  set B4 := install ser2Sl B3 o4 with hB4
  have b4h : ∀ j, B4 (ser2Sl j) = o4 j := fun j => install_slot _ ser2Sl_inj _ _ _
  have b4 : ∀ t : Fin 571, (t.val < 2 ∨ (3 < t.val ∧ t.val < 137) ∨ 264 ≤ t.val) → B4 t = B3 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; simp only [ser2Sl] at hv; have hj := j.isLt; split_ifs at hv <;> omega)
  have f4 : ∀ t : Fin 571, 264 ≤ t.val → B4 t = [] := fun t ht => by rw [b4 _ (by omega), f3 _ (by omega)]
  -- 5: copy it exact
  obtain ⟨o5, d5, -, m1, m2⟩ := cp_dock cp2Sl cp2Sl_inj KC.bits (List.replicate
    (PCPPairReusable.capacity (PCPSerializerMass.mass (gsOf k)) - (frame KC.bits).length) false) B4
    (by show B4 212 = _; rw [show (212 : Fin 571) = ser2Sl 77 from rfl, b4h, y77, code_gsOf]; rfl)
    (by show B4 7 = _; rw [b4 _ (by decide), h37])
    (by show B4 264 = _; rw [f4 _ (by decide)])
    (by show B4 265 = _; rw [f4 _ (by decide)])
  set B5 := install cp2Sl B4 o5 with hB5
  have b5h : ∀ j, B5 (cp2Sl j) = o5 j := fun j => install_slot _ cp2Sl_inj _ _ _
  have b5 : ∀ t : Fin 571, (∀ j, (cp2Sl j).val ≠ t.val) → B5 t = B4 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f5 : ∀ t : Fin 571, 266 ≤ t.val → B5 t = [] := fun t ht => by
    rw [b5 _ (by intro j; rw [cp2Sl_val]; fin_cases j <;> simp <;> omega), f4 _ (by omega)]
  have h57 : B5 7 = [false] := by rw [show (7 : Fin 571) = cp2Sl 1 from rfl, b5h, m1]
  have h5KC : B5 264 = frame KC.bits := by rw [show (264 : Fin 571) = cp2Sl 2 from rfl, b5h, m2]
  have h5BL : B5 135 = frame BL.bits := by
    rw [b5 _ (by intro j; rw [cp2Sl_val]; fin_cases j <;> decide), b4 _ (by decide), h3BL]
  have keep5 : ∀ t : Fin 571, 4 ≤ t.val → t.val < 7 → B5 t = B0 t := fun t h1 h2 => by
    rw [b5 _ (by intro j; rw [cp2Sl_val]; fin_cases j <;> simp <;> omega), b4 _ (by omega), keep3 _ (by omega) h2]
  -- 6: the constant `frame 0.bits`
  have d6 := NearCubicWires.WireExponent3_5.PrimT.cell_step.dock zSl zSl_inj (fun _ => 0) B5 (fun _ => rfl)
    (fun _ => f5 266 (by decide))
  rw [zeroH] at d6
  set B6 := install zSl B5 (fun _ => [false]) with hB6
  have b6 : ∀ t : Fin 571, t.val ≠ 266 → B6 t = B5 t := fun t ht =>
    install_other _ _ _ _ (fun _ e => ht (by rw [← e]; rfl))
  have h6z : B6 266 = [false] := install_slot zSl zSl_inj _ _ 0
  have f6 : ∀ t : Fin 571, 267 ≤ t.val → B6 t = [] := fun t ht => by rw [b6 _ (by omega), f5 _ (by omega)]
  -- 7: `cons topv 0`
  obtain ⟨o7, d7, pd7, q7⟩ := cons_dock 4 266 267 (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide⟩
    topv 0 B6 (by show B6 4 = _; rw [b6 _ (by decide), keep5 _ (by decide) (by decide)]; simp [hB0, sufIn])
    (by show B6 266 = _; rw [h6z]; rfl) (fun t h1 h2 => f6 t h1)
  set B7 := install c1Sl B6 o7 with hB7
  have b7h : ∀ j, B7 (c1Sl j) = o7 j := fun j => install_slot _ c1Sl_inj _ _ _
  have b7 : ∀ t : Fin 571, (t.val < 4 ∨ (4 < t.val ∧ t.val < 266) ∨ 341 ≤ t.val) → B7 t = B6 t := fun t ht =>
    install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; rw [show c1Sl = cSl 4 266 267 _ _ _ from rfl, cSl_val] at hv
      have hj := j.isLt; split_ifs at hv <;> omega)
  have f7 : ∀ t : Fin 571, 341 ≤ t.val → B7 t = [] := fun t ht => by rw [b7 _ (by omega), f6 _ (by omega)]
  -- 8: copy it exact
  obtain ⟨o8, d8, -, n1, n2⟩ := cp_dock cp3Sl cp3Sl_inj (cons topv 0).bits (List.replicate pd7 false) B7
    (by show B7 329 = _; rw [show (329 : Fin 571) = c1Sl 64 from rfl, b7h, q7])
    (by show B7 7 = _; rw [b7 _ (by decide), b6 _ (by decide), h57])
    (by show B7 341 = _; rw [f7 _ (by decide)])
    (by show B7 342 = _; rw [f7 _ (by decide)])
  set B8 := install cp3Sl B7 o8 with hB8
  have b8h : ∀ j, B8 (cp3Sl j) = o8 j := fun j => install_slot _ cp3Sl_inj _ _ _
  have b8 : ∀ t : Fin 571, (∀ j, (cp3Sl j).val ≠ t.val) → B8 t = B7 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f8 : ∀ t : Fin 571, 343 ≤ t.val → B8 t = [] := fun t ht => by
    rw [b8 _ (by intro j; rw [cp3Sl_val]; fin_cases j <;> simp <;> omega), f7 _ (by omega)]
  -- 9: `cons BL (cons topv 0)`
  obtain ⟨o9, d9, pd9, q9⟩ := cons_dock 135 341 343 (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ BL (cons topv 0) B8
    (by show B8 135 = _; rw [b8 _ (by intro j; rw [cp3Sl_val]; fin_cases j <;> decide), b7 _ (by decide),
      b6 _ (by decide), h5BL])
    (by show B8 341 = _; rw [show (341 : Fin 571) = cp3Sl 2 from rfl, b8h, n2]) (fun t h1 h2 => f8 t h1)
  set B9 := install c2Sl B8 o9 with hB9
  have b9h : ∀ j, B9 (c2Sl j) = o9 j := fun j => install_slot _ c2Sl_inj _ _ _
  have b9 : ∀ t : Fin 571, (t.val < 135 ∨ (135 < t.val ∧ t.val < 341) ∨ t.val = 342 ∨ 417 ≤ t.val) → B9 t = B8 t :=
    fun t ht => install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; rw [show c2Sl = cSl 135 341 343 _ _ _ from rfl, cSl_val] at hv
      have hj := j.isLt; split_ifs at hv <;> omega)
  have f9 : ∀ t : Fin 571, 417 ≤ t.val → B9 t = [] := fun t ht => by rw [b9 _ (by omega), f8 _ (by omega)]
  have h87 : B8 7 = [false] := by rw [show (7 : Fin 571) = cp3Sl 1 from rfl, b8h, n1]
  -- 10: copy it exact
  obtain ⟨o10, d10, -, u1, u2⟩ := cp_dock cp4Sl cp4Sl_inj (cons BL (cons topv 0)).bits (List.replicate pd9 false) B9
    (by show B9 405 = _; rw [show (405 : Fin 571) = c2Sl 64 from rfl, b9h, q9])
    (by show B9 7 = _; rw [b9 _ (by decide), h87])
    (by show B9 417 = _; rw [f9 _ (by decide)])
    (by show B9 418 = _; rw [f9 _ (by decide)])
  set B10 := install cp4Sl B9 o10 with hB10
  have b10h : ∀ j, B10 (cp4Sl j) = o10 j := fun j => install_slot _ cp4Sl_inj _ _ _
  have b10 : ∀ t : Fin 571, (∀ j, (cp4Sl j).val ≠ t.val) → B10 t = B9 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f10 : ∀ t : Fin 571, 419 ≤ t.val → B10 t = [] := fun t ht => by
    rw [b10 _ (by intro j; rw [cp4Sl_val]; fin_cases j <;> simp <;> omega), f9 _ (by omega)]
  -- 11: `cons KC ·`
  obtain ⟨o11, d11, pd11, q11⟩ := cons_dock 264 417 419 (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ KC (cons BL (cons topv 0)) B10
    (by show B10 264 = _; rw [b10 _ (by intro j; rw [cp4Sl_val]; fin_cases j <;> decide), b9 _ (by decide),
      b8 _ (by intro j; rw [cp3Sl_val]; fin_cases j <;> decide), b7 _ (by decide), b6 _ (by decide), h5KC])
    (by show B10 417 = _; rw [show (417 : Fin 571) = cp4Sl 2 from rfl, b10h, u2]) (fun t h1 h2 => f10 t h1)
  set B11 := install c3Sl B10 o11 with hB11
  have b11h : ∀ j, B11 (c3Sl j) = o11 j := fun j => install_slot _ c3Sl_inj _ _ _
  have b11 : ∀ t : Fin 571, (t.val < 264 ∨ (264 < t.val ∧ t.val < 417) ∨ t.val = 418 ∨ 493 ≤ t.val) →
      B11 t = B10 t := fun t ht => install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; rw [show c3Sl = cSl 264 417 419 _ _ _ from rfl, cSl_val] at hv
      have hj := j.isLt; split_ifs at hv <;> omega)
  have f11 : ∀ t : Fin 571, 493 ≤ t.val → B11 t = [] := fun t ht => by rw [b11 _ (by omega), f10 _ (by omega)]
  have h107 : B10 7 = [false] := by rw [show (7 : Fin 571) = cp4Sl 1 from rfl, b10h, u1]
  -- 12: copy it exact
  obtain ⟨o12, d12, -, v1, v2⟩ := cp_dock cp5Sl cp5Sl_inj (cons KC (cons BL (cons topv 0))).bits
    (List.replicate pd11 false) B11
    (by show B11 481 = _; rw [show (481 : Fin 571) = c3Sl 64 from rfl, b11h, q11])
    (by show B11 7 = _; rw [b11 _ (by decide), h107])
    (by show B11 493 = _; rw [f11 _ (by decide)])
    (by show B11 494 = _; rw [f11 _ (by decide)])
  set B12 := install cp5Sl B11 o12 with hB12
  have b12h : ∀ j, B12 (cp5Sl j) = o12 j := fun j => install_slot _ cp5Sl_inj _ _ _
  have b12 : ∀ t : Fin 571, (∀ j, (cp5Sl j).val ≠ t.val) → B12 t = B11 t := fun t ht =>
    install_other _ _ _ _ (fun j e => ht j (congrArg Fin.val e))
  have f12 : ∀ t : Fin 571, 495 ≤ t.val → B12 t = [] := fun t ht => by
    rw [b12 _ (by intro j; rw [cp5Sl_val]; fin_cases j <;> simp <;> omega), f11 _ (by omega)]
  -- 13: `cons tagv ·`
  obtain ⟨o13, d13, pd13, q13⟩ := cons_dock 5 493 495 (by decide) (by decide) (by decide) (by decide)
    ⟨by decide, by decide⟩ tagv (cons KC (cons BL (cons topv 0))) B12
    (by show B12 5 = _
        rw [b12 _ (by intro j; rw [cp5Sl_val]; fin_cases j <;> decide), b11 _ (by decide),
          b10 _ (by intro j; rw [cp4Sl_val]; fin_cases j <;> decide), b9 _ (by decide),
          b8 _ (by intro j; rw [cp3Sl_val]; fin_cases j <;> decide), b7 _ (by decide), b6 _ (by decide),
          keep5 _ (by decide) (by decide)]
        simp [hB0, sufIn])
    (by show B12 493 = _; rw [show (493 : Fin 571) = cp5Sl 2 from rfl, b12h, v2]) (fun t h1 h2 => f12 t h1)
  set B13 := install c4Sl B12 o13 with hB13
  have b13h : ∀ j, B13 (c4Sl j) = o13 j := fun j => install_slot _ c4Sl_inj _ _ _
  have b13 : ∀ t : Fin 571, (t.val < 5 ∨ (5 < t.val ∧ t.val < 493) ∨ t.val = 494 ∨ 569 ≤ t.val) → B13 t = B12 t :=
    fun t ht => install_other _ _ _ _ (fun j e => by
      have hv := congrArg Fin.val e; rw [show c4Sl = cSl 5 493 495 _ _ _ from rfl, cSl_val] at hv
      have hj := j.isLt; split_ifs at hv <;> omega)
  have h127 : B12 7 = [false] := by rw [show (7 : Fin 571) = cp5Sl 1 from rfl, b12h, v1]
  -- 14: the `natWord` writer
  obtain ⟨o14, s14, -, -, w2⟩ := natStage (sufCode accL k topv tagv) (List.replicate pd13 false)
  have d14 := s14.dock natSl natSl_inj (fun _ => 0) B13 (fun _ => rfl) (by
    intro j; rw [natIn_val]
    fin_cases j
    · show B13 557 = _; rw [show (557 : Fin 571) = c4Sl 64 from rfl, b13h, q13]; rfl
    · show B13 7 = _; rw [b13 _ (by decide), h127]; rfl
    · show B13 6 = _
      rw [b13 _ (by decide), b12 _ (by intro j; rw [cp5Sl_val]; fin_cases j <;> decide), b11 _ (by decide),
        b10 _ (by intro j; rw [cp4Sl_val]; fin_cases j <;> decide), b9 _ (by decide),
        b8 _ (by intro j; rw [cp3Sl_val]; fin_cases j <;> decide), b7 _ (by decide), b6 _ (by decide),
        keep5 _ (by decide) (by decide)]
      simp [hB0, sufIn]
    · show B13 569 = _; rw [b13 _ (by decide), f12 _ (by decide)]; rfl
    · show B13 570 = _; rw [b13 _ (by decide), f12 _ (by decide)]; rfl)
  rw [zeroH] at d14
  have run := d1.seq (d2.seq (d3.seq (d4.seq (d5.seq (d6.seq (d7.seq (d8.seq (d9.seq (d10.seq (d11.seq (d12.seq
    (d13.seq d14))))))))))))
  set B14 := install natSl B13 o14 with hB14
  have run' : Step sufM _ (fun _ => 0) B0 (fun _ => 0) B14 := run
  refine ⟨B14, ?_, ?_⟩
  · exact run'.enlarge (by unfold sufCost; exact le_refl _)
  · rw [show (6 : Fin 571) = natSl 2 from rfl]
    exact (install_slot natSl natSl_inj B13 o14 2).trans w2

end NearCubicWires.WireExponent3_5.UnionMachine.CWParSuf
