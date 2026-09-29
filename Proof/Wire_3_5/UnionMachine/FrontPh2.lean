import Proof.Wire_3_5.UnionMachine.FrontPh1
import Proof.Wire_3_5.UnionMachine.FrontHierarchy
import Proof.Wire_3_5.UnionMachine.FrontCapStage
import Proof.Wire_3_5.UnionMachine.FrontG3

/-! # C6 front, the chain, phase 2: the hierarchy word, the capacity, the PCPP output (P3:3632-3653, 3669-3672)

On five regions after phase 1 (whose `1^q` and oracle descriptor are shared tapes `tq`, `td`):
1. a copy of `frame x`; 2. the hierarchy word `frame (hierarchyInput H ⟨N, x⟩)` (`FrontHierarchy.hier_ready`, on the
copy); 3. the capacity `1^{64(q+|x|)}` (`FrontCapStage.cap_ready`, sharing `x`, `1^q`); 4. a copy of `1^q` (base's
`ClockUnarySum.sum_ready q 0`); 5. The padded source (`FrontG3.g3_step`) on the hierarchy word, the descriptor,
the copy of `1^q` and the capacity: the PCPP output word `pcppOutput request (a.output request)` at head `0`.
**`ph2_step`**: the run and the PCPP word; `x`, `1^q` kept; every tape below the regions but the descriptor
untouched; the front's tapes past the regions blank.

Paper quantity: the PCPP output of the substituted circuit of the guessed oracle (P3:3672). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontPh2
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.RepairSource NearCubicWires.SourceInterfaces NearCubicWires.RepairSource.ProjectionNormalization
open NearCubicWires.WireExponent3_5.Transfer.CaseTwoPadG
open NearCubicWires.RepairRepresentation NearCubicWires.RepairOrdinary.CloseoutCaseTwo
open NearCubicWires.WireExponent3_5.UnionMachine.FrontPh1 (xT xT_val)

section Ph
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (source : ProjectionSourceAlgorithm UWhole.verifier UWhole.time) (a : PointwisePCPPAlgorithm) (k k0 : ℕ)

/-- The phase's size. -/
noncomputable abbrev PH2 : ℕ := 4 + FrontHierarchy.HT k + FrontCapStage.CT + 4 + gtapes source a k

/-- The regions' offsets. -/
noncomputable abbrev oH : ℕ := k0 + 4
noncomputable abbrev oC : ℕ := k0 + 4 + FrontHierarchy.HT k
noncomputable abbrev oQ : ℕ := k0 + 4 + FrontHierarchy.HT k + FrontCapStage.CT
noncomputable abbrev oG : ℕ := k0 + 4 + FrontHierarchy.HT k + FrontCapStage.CT + 4

theorem hA (h : k0 + PH2 source a k ≤ tf) : k0 + 4 ≤ tf := by unfold PH2 at h; omega
theorem hB (h : k0 + PH2 source a k ≤ tf) : oH k0 + FrontHierarchy.HT k ≤ tf := by unfold PH2 at h; unfold oH; omega
theorem hC (h : k0 + PH2 source a k ≤ tf) : oC k k0 + FrontCapStage.CT ≤ tf := by unfold PH2 at h; unfold oC; omega
theorem hD (h : k0 + PH2 source a k ≤ tf) : oQ k k0 + 4 ≤ tf := by unfold PH2 at h; unfold oQ; omega
theorem hE (h : k0 + PH2 source a k ≤ tf) : oG k k0 + gtapes source a k ≤ tf := by unfold PH2 at h; unfold oG; omega

variable (h : k0 + PH2 source a k ≤ tf) (tq td : Fin (NW P tf))

/-- The copy of `x`, the hierarchy word, the capacity, the copy of `1^q`. -/
noncomputable def cx : Fin (NW P tf) := rg P tf k0 (hA tf source a k k0 h) (1 : Fin 4)
noncomputable def hw : Fin (NW P tf) := rg P tf (oH k0) (hB tf source a k k0 h) (FrontHierarchy.hOut k)
noncomputable def cp : Fin (NW P tf) := rg P tf (oC k k0) (hC tf source a k k0 h) (20 : Fin FrontCapStage.CT)
noncomputable def qc : Fin (NW P tf) := rg P tf (oQ k k0) (hD tf source a k k0 h) (2 : Fin 4)

noncomputable def shA (j : Fin 4) : Option (Fin (NW P tf)) := if j.val = 0 then some (xT P tf) else none
noncomputable def shB (j : Fin (FrontHierarchy.HT k)) : Option (Fin (NW P tf)) :=
  if j.val = 2 then some (cx P tf source a k k0 h) else none
noncomputable def shC (j : Fin FrontCapStage.CT) : Option (Fin (NW P tf)) :=
  if j.val = 0 then some (xT P tf) else if j.val = 1 then some tq else none
noncomputable def shD (j : Fin 4) : Option (Fin (NW P tf)) := if j.val = 0 then some tq else none
noncomputable def shE (j : Fin (gtapes source a k)) : Option (Fin (NW P tf)) :=
  if j = gWidth source a k then some (qc P tf source a k k0 h)
  else if j = gHier source a k then some (hw P tf source a k k0 h)
  else if j = gDesc source a k then some td
  else if j = gCap source a k then some (cp P tf source a k k0 h) else none

theorem hw_val : (hw P tf source a k k0 h).val = 2 + NL P + (oH k0 + (FrontHierarchy.hOut k).val) := rfl
theorem cp_val : (cp P tf source a k k0 h).val = 2 + NL P + (oC k k0 + 20) := rfl
theorem qc_val : (qc P tf source a k k0 h).val = 2 + NL P + (oQ k k0 + 2) := rfl

/-! ## Injectivity -/

theorem shA_some (j : Fin 4) (b : Fin (NW P tf)) (hj : shA P tf j = some b) : j.val = 0 ∧ b.val = 0 := by
  unfold shA at hj; split_ifs at hj with a0; cases hj; exact ⟨a0, rfl⟩

theorem shB_some (j : Fin (FrontHierarchy.HT k)) (b : Fin (NW P tf)) (hj : shB P tf source a k k0 h j = some b) :
    j.val = 2 ∧ b.val = 2 + NL P + (k0 + 1) := by
  unfold shB at hj; split_ifs at hj with a0; cases hj; exact ⟨a0, rfl⟩

theorem shC_some (j : Fin FrontCapStage.CT) (b : Fin (NW P tf)) (hj : shC P tf tq j = some b) :
    (j.val = 0 ∧ b.val = 0) ∨ (j.val = 1 ∧ b = tq) := by
  unfold shC at hj; split_ifs at hj with a0 a1 <;> cases hj
  · exact Or.inl ⟨a0, rfl⟩
  · exact Or.inr ⟨a1, rfl⟩

theorem shD_some (j : Fin 4) (b : Fin (NW P tf)) (hj : shD P tf tq j = some b) : j.val = 0 ∧ b = tq := by
  unfold shD at hj; split_ifs at hj with a0; cases hj; exact ⟨a0, rfl⟩

theorem shE_some (j : Fin (gtapes source a k)) (b : Fin (NW P tf)) (hj : shE P tf source a k k0 h td j = some b) :
    (j = gWidth source a k ∧ b.val = 2 + NL P + (oQ k k0 + 2)) ∨
      (j = gHier source a k ∧ b.val = 2 + NL P + (oH k0 + (FrontHierarchy.hOut k).val)) ∨
      (j = gDesc source a k ∧ b.val = td.val) ∨ (j = gCap source a k ∧ b.val = 2 + NL P + (oC k k0 + 20)) := by
  unfold shE at hj
  split_ifs at hj with a0 a1 a2 a3 <;> cases hj
  · exact Or.inl ⟨a0, rfl⟩
  · exact Or.inr (Or.inl ⟨a1, rfl⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a2, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a3, rfl⟩))

theorem slA_inj : Function.Injective (sl P tf (shA P tf) k0 (hA tf source a k k0 h)) := by
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (fun i b hi => ?_)
  · have := shA_some P tf i b hi; have := shA_some P tf j b hj; exact Fin.ext (by omega)
  · have := shA_some P tf i b hi; omega

theorem slB_inj : Function.Injective (sl P tf (shB P tf source a k k0 h) (oH k0) (hB tf source a k k0 h)) := by
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (fun i b hi => ?_)
  · have := shB_some P tf source a k k0 h i b hi; have := shB_some P tf source a k k0 h j b hj
    exact Fin.ext (by omega)
  · have := shB_some P tf source a k k0 h i b hi; unfold oH; omega

theorem slC_inj (htq : 2 + NL P ≤ tq.val ∧ tq.val < 2 + NL P + k0) : Function.Injective (sl P tf (shC P tf tq) (oC k k0) (hC tf source a k k0 h)) := by
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (fun i b hi => ?_)
  · apply Fin.ext
    rcases shC_some P tf tq i b hi with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;>
    rcases shC_some P tf tq j b hj with ⟨v1, v2⟩ | ⟨v1, v2⟩
    · omega
    · subst v2; omega
    · subst u2; omega
    · omega
  · unfold oC
    rcases shC_some P tf tq i b hi with ⟨_, u2⟩ | ⟨_, u2⟩
    · omega
    · subst u2; omega

theorem slD_inj (htq : 2 + NL P ≤ tq.val ∧ tq.val < 2 + NL P + k0) : Function.Injective (sl P tf (shD P tf tq) (oQ k k0) (hD tf source a k k0 h)) := by
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (fun i b hi => ?_)
  · have := shD_some P tf tq i b hi; have := shD_some P tf tq j b hj; exact Fin.ext (by omega)
  · unfold oQ; obtain ⟨_, u⟩ := shD_some P tf tq i b hi; subst u; omega

theorem gdist : (gWidth source a k).val ≠ (gHier source a k).val ∧ (gWidth source a k).val ≠ (gDesc source a k).val ∧
    (gWidth source a k).val ≠ (gCap source a k).val ∧ (gHier source a k).val ≠ (gDesc source a k).val ∧
    (gHier source a k).val ≠ (gCap source a k).val ∧ (gDesc source a k).val ≠ (gCap source a k).val := by
  have := (gw_lt source a k).2
  simp only [gWidth, gHier, gDesc, gCap]
  omega

theorem off_eqs : oH k0 = k0 + 4 ∧ oC k k0 = oH k0 + FrontHierarchy.HT k ∧ oQ k k0 = oC k k0 + FrontCapStage.CT ∧
    oG k k0 = oQ k k0 + 4 ∧ FrontCapStage.CT = 22 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem slE_inj (htd : 2 + NL P ≤ td.val ∧ td.val < 2 + NL P + k0) : Function.Injective
    (sl P tf (shE P tf source a k k0 h td) (oG k k0) (hE tf source a k k0 h)) := by
  have hO := (FrontHierarchy.hOut k).isLt
  have ho := off_eqs k k0
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (fun i b hi => ?_)
  · rcases shE_some P tf source a k k0 h td i b hi with ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ <;>
    rcases shE_some P tf source a k k0 h td j b hj with ⟨v1, v2⟩ | ⟨v1, v2⟩ | ⟨v1, v2⟩ | ⟨v1, v2⟩
    all_goals first
      | (exfalso; omega)
      | (rw [u1, v1])
  · rcases shE_some P tf source a k k0 h td i b hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega

/-! ## The phase's machine -/

/-- **Phase 2**: copy `x`, the hierarchy word, the capacity, copy `1^q`, the padded source. -/
noncomputable def ph2M (H : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) :=
  Composition.machine (RecoveryFocus.machine (sl P tf (shA P tf) k0 (hA tf source a k k0 h))
    RecoveryColdWitnessCopy.machine)
  (Composition.machine (RecoveryFocus.machine (sl P tf (shB P tf source a k k0 h) (oH k0) (hB tf source a k k0 h))
    (FrontHierarchy.hierMachine k H.coefficient))
  (Composition.machine (RecoveryFocus.machine (sl P tf (shC P tf tq) (oC k k0) (hC tf source a k k0 h))
    FrontCapStage.capMachine)
  (Composition.machine (RecoveryFocus.machine (sl P tf (shD P tf tq) (oQ k k0) (hD tf source a k k0 h))
    ClockUnarySum.machine)
    (RecoveryFocus.machine (sl P tf (shE P tf source a k k0 h td) (oG k k0) (hE tf source a k k0 h))
      (omachineG source a k H.coefficient Cpad (VerifierEncoding.code H.verifier))))))

/-! ## Entries -/

theorem req_input_val (bits : List Bool) (j : Fin (CloseoutHierarchyRequest.tapes k)) :
    CloseoutHierarchyRequest.input k bits j = if j.val = 2 then RepairOrdinary.frame bits else [] := by
  have h35 := RepairOrdinary.HierarchyFromInput.tapes_lower (k + 2)
  unfold CloseoutHierarchyRequest.input
  refine Fin.addCases (fun j1 => ?_) (fun j2 => ?_) j
  · rw [Fin.addCases_left, Fin.val_castAdd]
    unfold CloseoutHierarchyClock.Input.input
    refine Fin.addCases (fun j3 => ?_) (fun j4 => ?_) j1
    · rw [Fin.addCases_left, Fin.val_castAdd]
      simp only [RepairOrdinary.HierarchyFromInput.input]
    · rw [Fin.addCases_right, Fin.val_natAdd, if_neg (by omega)]
  · rw [Fin.addCases_right, Fin.val_natAdd, if_neg (by unfold CloseoutHierarchyClock.Input.tapes; omega)]

theorem hInput_val (bits : List Bool) (i : Fin (FrontHierarchy.HT k)) :
    FrontHierarchy.hInput k bits i = if i.val = 2 then RepairOrdinary.frame bits else [] := by
  have h35 := RepairOrdinary.HierarchyFromInput.tapes_lower (k + 2)
  unfold FrontHierarchy.hInput
  split_ifs with h1 h2 h2
  · rw [req_input_val, if_pos h2]
  · rw [req_input_val, if_neg h2]
  · exfalso; apply h1
    show i.val < CloseoutHierarchyRequest.tapes k
    unfold CloseoutHierarchyRequest.tapes CloseoutHierarchyClock.Input.tapes; omega
  · rfl

theorem sum_in (q : ℕ) (j : Fin 4) :
    (![List.replicate q true, List.replicate 0 true, [], []] : Fin 4 → List Bool) j =
      if j.val = 0 then List.replicate q true else [] := by
  fin_cases j <;> rfl

theorem clauseData_zero (src : List Bool) (ar C : ℕ) :
    PCPPQueryIndexPadding.clauseData src ar 0 C [] 0 = src := by
  simp [PCPPQueryIndexPadding.clauseData, PCPPQueryClauseReuse.data]

theorem heads_zero : PCPPQueryClauseReuse.heads 0 = 0 := by decide

/-- The PCPP output word's tape: the image of the padded source's cache tape `0`. -/
noncomputable def poT : Fin (NW P tf) :=
  sl P tf (shE P tf source a k k0 h td) (oG k k0) (hE tf source a k k0 h)
    (oslotsG source a k (RequestSource.cacheSlots a (SourceCache.cacheSlots a 0)))

/-- **Phase 2's run.** -/
theorem ph2_step (Hh : OrdinaryHierarchy (fun n => n ^ (k + 2))) (Cpad : ℕ) (hcoeff : Hh.coefficient ≤ Cpad)
    (hpad : k + 3 ≤ Cpad) {N : ℕ} (x : BitInput N) (q : ℕ)
    (hq : PCPPNativeHierarchyNodes.width source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x ≤ q)
    (O : BooleanCircuit q) (hcap : 64 * (O.size + q + 4) + 1 ≤ FrontCapStage.capOf (List.ofFn x) q)
    (Ha : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hP : PristineH P tf Ha A k0)
    (hx : A (xT P tf) = RepairOrdinary.frame (List.ofFn x)) (hxH : Ha (xT P tf) = 0)
    (htq : 2 + NL P ≤ tq.val ∧ tq.val < 2 + NL P + k0) (hqA : A tq = List.replicate q true) (hqH : Ha tq = 0)
    (htd : 2 + NL P ≤ td.val ∧ td.val < 2 + NL P + k0) (hdA : A td = PCPPNative.descriptor O) (hdH : Ha td = 0)
    (htqd : tq ≠ td) :
    let request := PCPPRequestBoundary.request a
      (padSubstituted source k Hh.coefficient Cpad (VerifierEncoding.code Hh.verifier) x hpad hq O)
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (ph2M P tf source a k k0 h tq td Hh Cpad) ((8 * (List.ofFn x).length + 14) + 1 +
        (FrontHierarchy.hierCost k Hh.coefficient (List.ofFn x) (Hh.time N) + 1 +
          (FrontCapStage.capCost (List.ofFn x) q + 1 + ((2 * (q + 0) + 6) + 1 +
            obudgetG source a Hh Cpad hpad ⟨N, x⟩ hq O (FrontCapStage.capOf (List.ofFn x) q))))) Ha A H' A' ∧
      PristineH P tf H' A' (k0 + PH2 source a k) ∧
      (A' (poT P tf source a k k0 h td) = pcppOutput request (a.output request) ∧
        H' (poT P tf source a k k0 h td) = 0) ∧
      (A' (xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H' (xT P tf) = 0) ∧
      (A' tq = List.replicate q true ∧ H' tq = 0) ∧
      ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + k0 → y ≠ td → A' y = A y ∧ H' y = Ha y := by
  intro request
  have hxL : (xT P tf).val < 2 := by rw [xT_val]; omega
  have ho := off_eqs k k0
  have hOl := (FrontHierarchy.hOut k).isLt
  -- stage 1: the copy of `x`
  have i1 := slA_inj P tf source a k k0 h
  have hlow1 : ∀ i b, shA P tf i = some b → b.val < 2 + NL P + k0 := fun i b hi => by
    have := shA_some P tf i b hi; omega
  have hL1 : ∀ i b, shA P tf i = some b → 2 + NL P ≤ b.val ∨ b.val < 2 := fun i b hi => by
    have := shA_some P tf i b hi; omega
  have sA0 : shA P tf (0 : Fin 4) = some (xT P tf) := rfl
  have r1 := dockAny (FrontLoopKit.step_of_rready (RecoveryColdWitnessCopy.copy_ready (List.ofFn x))) _ i1 Ha A
    (fun j => by
      by_cases hj : j.val = 0
      · rw [show j = 0 from Fin.ext hj, sl_some P tf _ k0 _ 0 _ sA0]; exact hxH
      · rw [sl_none P tf _ k0 _ j (by simp [shA, hj])]; exact (pristineH_rg P tf k0 _ Ha A hP j).2)
    (fun j => by
      rw [FrontPh1.copy_in]
      by_cases hj : j.val = 0
      · rw [if_pos hj, show j = 0 from Fin.ext hj, sl_some P tf _ k0 _ 0 _ sA0]; exact hx
      · rw [if_neg hj, sl_none P tf _ k0 _ j (by simp [shA, hj])]; exact (pristineH_rg P tf k0 _ Ha A hP j).1)
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = dockH (sl P tf (shA P tf) k0 (hA tf source a k k0 h)) Ha (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = install (sl P tf (shA P tf) k0 (hA tf source a k k0 h)) A
      (RecoveryColdWitnessCopy.output (List.ofFn x)) := ⟨_, rfl⟩
  rw [← hH1, ← hA1] at r1
  have P1 : PristineH P tf H1 A1 (k0 + 4) := by
    rw [hH1, hA1]; exact pristineH_after P tf _ k0 _ hlow1 hL1 Ha A _ _ hP
  have lo1 : ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + k0 → A1 y = A y ∧ H1 y = Ha y := by
    intro y hy1 hy2
    have hns : ∀ i b, shA P tf i = some b → b ≠ y := fun i b hi e => by
      have := shA_some P tf i b hi; rw [e] at this; omega
    rw [hA1, hH1]
    exact ⟨install_low P tf _ k0 _ A _ y hy2 hns, dockH_low P tf _ k0 _ Ha _ y hy2 hns⟩
  have a1x : A1 (xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H1 (xT P tf) = 0 := by
    rw [hA1, hH1, install_sh P tf _ k0 _ i1 A _ 0 _ sA0, dockH_sh P tf _ k0 _ i1 Ha _ 0 _ sA0]; exact ⟨rfl, rfl⟩
  have a1c : A1 (cx P tf source a k k0 h) = RepairOrdinary.frame (List.ofFn x) ∧ H1 (cx P tf source a k k0 h) = 0 := by
    rw [hA1, hH1, cx, install_rg P tf _ k0 _ i1 A _ 1 rfl, dockH_rg P tf _ k0 _ i1 Ha _ 1 rfl]
    exact ⟨rfl, rfl⟩
  -- stage 2: the hierarchy word
  obtain ⟨out2, g2, o2⟩ := FrontHierarchy.hier_ready k Hh x
  have i2 := slB_inj P tf source a k k0 h
  have hlow2 : ∀ i b, shB P tf source a k k0 h i = some b → b.val < 2 + NL P + oH k0 := fun i b hi => by
    have := shB_some P tf source a k k0 h i b hi; omega
  have hL2 : ∀ i b, shB P tf source a k k0 h i = some b → 2 + NL P ≤ b.val ∨ b.val < 2 := fun i b hi => by
    have := shB_some P tf source a k k0 h i b hi; omega
  have r2 := dockAnyR g2 _ i2 H1 A1
    (fun j => by
      by_cases hj : j.val = 2
      · rw [sl_some P tf _ _ _ j (cx P tf source a k k0 h) (by simp [shB, hj])]; exact a1c.2
      · rw [sl_none P tf _ _ _ j (by simp [shB, hj])]; exact (pristineH_rg P tf _ _ H1 A1 P1 j).2)
    (fun j => by
      rw [hInput_val]
      by_cases hj : j.val = 2
      · rw [if_pos hj, sl_some P tf _ _ _ j (cx P tf source a k k0 h) (by simp [shB, hj])]; exact a1c.1
      · rw [if_neg hj, sl_none P tf _ _ _ j (by simp [shB, hj])]; exact (pristineH_rg P tf _ _ H1 A1 P1 j).1)
  obtain ⟨H2, hH2⟩ : ∃ H2, H2 = dockH (sl P tf (shB P tf source a k k0 h) (oH k0) (hB tf source a k k0 h)) H1
      (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = install (sl P tf (shB P tf source a k k0 h) (oH k0) (hB tf source a k k0 h)) A1 out2 :=
    ⟨_, rfl⟩
  rw [← hH2, ← hA2] at r2
  have P2 : PristineH P tf H2 A2 (oH k0 + FrontHierarchy.HT k) := by
    rw [hH2, hA2]; exact pristineH_after P tf _ _ _ hlow2 hL2 H1 A1 _ _ P1
  have lo2 : ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + k0 → A2 y = A1 y ∧ H2 y = H1 y := by
    intro y hy1 hy2
    have hns : ∀ i b, shB P tf source a k k0 h i = some b → b ≠ y := fun i b hi e => by
      have := shB_some P tf source a k k0 h i b hi; rw [e] at this; omega
    rw [hA2, hH2]
    exact ⟨install_low P tf _ _ _ A1 _ y (by omega) hns, dockH_low P tf _ _ _ H1 _ y (by omega) hns⟩
  have a2x : A2 (xT P tf) = A1 (xT P tf) ∧ H2 (xT P tf) = H1 (xT P tf) := by
    have hns : ∀ i b, shB P tf source a k k0 h i = some b → b ≠ xT P tf := fun i b hi e => by
      have := shB_some P tf source a k k0 h i b hi; rw [e, xT_val] at this; omega
    rw [hA2, hH2]
    exact ⟨install_low P tf _ _ _ A1 _ _ (by omega) hns, dockH_low P tf _ _ _ H1 _ _ (by omega) hns⟩
  have a2h : A2 (hw P tf source a k k0 h) =
      RepairOrdinary.frame (HierarchySourceInput.hierarchyInput Hh ⟨N, x⟩) ∧ H2 (hw P tf source a k k0 h) = 0 := by
    have hn : shB P tf source a k k0 h (FrontHierarchy.hOut k) = none := by
      have hv : (FrontHierarchy.hOut k).val = FrontHierarchy.rT k + 3 := by
        simp [FrontHierarchy.hOut, FrontHierarchy.frs, FrontHierarchy.fx]
      have h35 := RepairOrdinary.HierarchyFromInput.tapes_lower (k + 2)
      have hr : 35 ≤ FrontHierarchy.rT k := by
        unfold FrontHierarchy.rT CloseoutHierarchyRequest.tapes CloseoutHierarchyClock.Input.tapes; omega
      simp only [shB]; rw [if_neg (by rw [hv]; omega)]
    rw [hA2, hH2, hw, install_rg P tf _ _ _ i2 A1 _ _ hn, dockH_rg P tf _ _ _ i2 H1 _ _ hn]
    exact ⟨o2, rfl⟩
  -- stage 3: the capacity
  obtain ⟨out3, g3, o20, o0, o1⟩ := FrontCapStage.cap_ready (List.ofFn x) q
  have i3 := slC_inj P tf source a k k0 h tq htq
  have hlow3 : ∀ i b, shC P tf tq i = some b → b.val < 2 + NL P + oC k k0 := fun i b hi => by
    rcases shC_some P tf tq i b hi with ⟨_, u⟩ | ⟨_, u⟩
    · omega
    · subst u; omega
  have hL3 : ∀ i b, shC P tf tq i = some b → 2 + NL P ≤ b.val ∨ b.val < 2 := fun i b hi => by
    rcases shC_some P tf tq i b hi with ⟨_, u⟩ | ⟨_, u⟩
    · omega
    · subst u; omega
  have e2q := lo2 tq (by omega) htq.2
  have e1q := lo1 tq (by omega) htq.2
  have sC0 : shC P tf tq (0 : Fin FrontCapStage.CT) = some (xT P tf) := rfl
  have sC1 : shC P tf tq (1 : Fin FrontCapStage.CT) = some tq := rfl
  have r3 := dockAnyR g3 _ i3 H2 A2
    (fun j => by
      by_cases j0 : j.val = 0
      · rw [sl_some P tf _ _ _ j (xT P tf) (by simp [shC, j0]), a2x.2, a1x.2]
      · by_cases j1 : j.val = 1
        · rw [sl_some P tf _ _ _ j tq (by simp [shC, j1]), e2q.2, e1q.2, hqH]
        · rw [sl_none P tf _ _ _ j (by simp [shC, j0, j1])]; exact (pristineH_rg P tf _ _ H2 A2 P2 j).2)
    (fun j => by
      simp only [FrontCapStage.capIn]
      by_cases j0 : j.val = 0
      · rw [if_pos j0, sl_some P tf _ _ _ j (xT P tf) (by simp [shC, j0]), a2x.1, a1x.1]
      · by_cases j1 : j.val = 1
        · rw [if_neg j0, if_pos j1, sl_some P tf _ _ _ j tq (by simp [shC, j1]), e2q.1, e1q.1, hqA]
        · rw [if_neg j0, if_neg j1, sl_none P tf _ _ _ j (by simp [shC, j0, j1])]
          exact (pristineH_rg P tf _ _ H2 A2 P2 j).1)
  obtain ⟨H3, hH3⟩ : ∃ H3, H3 = dockH (sl P tf (shC P tf tq) (oC k k0) (hC tf source a k k0 h)) H2 (fun _ => 0) :=
    ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A3, A3 = install (sl P tf (shC P tf tq) (oC k k0) (hC tf source a k k0 h)) A2 out3 := ⟨_, rfl⟩
  rw [← hH3, ← hA3] at r3
  have P3 : PristineH P tf H3 A3 (oC k k0 + FrontCapStage.CT) := by
    rw [hH3, hA3]; exact pristineH_after P tf _ _ _ hlow3 hL3 H2 A2 _ _ P2
  have lo3 : ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + oC k k0 → y ≠ tq → A3 y = A2 y ∧ H3 y = H2 y := by
    intro y hy1 hy2 hyq
    have hns : ∀ i b, shC P tf tq i = some b → b ≠ y := fun i b hi e => by
      rcases shC_some P tf tq i b hi with ⟨_, u⟩ | ⟨_, u⟩
      · rw [e] at u; omega
      · exact hyq (e.symm.trans u)
    rw [hA3, hH3]
    exact ⟨install_low P tf _ _ _ A2 _ y hy2 hns, dockH_low P tf _ _ _ H2 _ y hy2 hns⟩
  have a3x : A3 (xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H3 (xT P tf) = 0 := by
    rw [hA3, hH3, install_sh P tf _ _ _ i3 A2 _ 0 _ sC0, dockH_sh P tf _ _ _ i3 H2 _ 0 _ sC0]; exact ⟨o0, rfl⟩
  have a3q : A3 tq = List.replicate q true ∧ H3 tq = 0 := by
    rw [hA3, hH3, install_sh P tf _ _ _ i3 A2 _ 1 _ sC1, dockH_sh P tf _ _ _ i3 H2 _ 1 _ sC1]; exact ⟨o1, rfl⟩
  have a3c : A3 (cp P tf source a k k0 h) = List.replicate (FrontCapStage.capOf (List.ofFn x) q) true ∧
      H3 (cp P tf source a k k0 h) = 0 := by
    rw [hA3, hH3, cp, install_rg P tf _ _ _ i3 A2 _ _ rfl, dockH_rg P tf _ _ _ i3 H2 _ _ rfl]
    exact ⟨o20, rfl⟩
  -- stage 4: the copy of `1^q`
  have g4 := ClockUnarySum.sum_ready q 0
  have i4 := slD_inj P tf source a k k0 h tq htq
  have hlow4 : ∀ i b, shD P tf tq i = some b → b.val < 2 + NL P + oQ k k0 := fun i b hi => by
    obtain ⟨_, u⟩ := shD_some P tf tq i b hi; subst u; omega
  have hL4 : ∀ i b, shD P tf tq i = some b → 2 + NL P ≤ b.val ∨ b.val < 2 := fun i b hi => by
    obtain ⟨_, u⟩ := shD_some P tf tq i b hi; subst u; omega
  have sD0 : shD P tf tq (0 : Fin 4) = some tq := rfl
  have r4 := dockAnyR g4 _ i4 H3 A3
    (fun j => by
      by_cases j0 : j.val = 0
      · rw [sl_some P tf _ _ _ j tq (by simp [shD, j0])]; exact a3q.2
      · rw [sl_none P tf _ _ _ j (by simp [shD, j0])]; exact (pristineH_rg P tf _ _ H3 A3 P3 j).2)
    (fun j => by
      rw [sum_in]
      by_cases j0 : j.val = 0
      · rw [if_pos j0, sl_some P tf _ _ _ j tq (by simp [shD, j0])]; exact a3q.1
      · rw [if_neg j0, sl_none P tf _ _ _ j (by simp [shD, j0])]; exact (pristineH_rg P tf _ _ H3 A3 P3 j).1)
  obtain ⟨H4, hH4⟩ : ∃ H4, H4 = dockH (sl P tf (shD P tf tq) (oQ k k0) (hD tf source a k k0 h)) H3 (fun _ => 0) :=
    ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A4, A4 = install (sl P tf (shD P tf tq) (oQ k k0) (hD tf source a k k0 h)) A3
      ![List.replicate q true, List.replicate 0 true, List.replicate (q + 0) true, List.replicate (q + 0 + 2) false] :=
    ⟨_, rfl⟩
  rw [← hH4, ← hA4] at r4
  have P4 : PristineH P tf H4 A4 (oQ k k0 + 4) := by
    rw [hH4, hA4]; exact pristineH_after P tf _ _ _ hlow4 hL4 H3 A3 _ _ P3
  have lo4 : ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + oQ k k0 → y ≠ tq → A4 y = A3 y ∧ H4 y = H3 y := by
    intro y hy1 hy2 hyq
    have hns : ∀ i b, shD P tf tq i = some b → b ≠ y := fun i b hi e => by
      obtain ⟨_, u⟩ := shD_some P tf tq i b hi; exact hyq (e.symm.trans u)
    rw [hA4, hH4]
    exact ⟨install_low P tf _ _ _ A3 _ y hy2 hns, dockH_low P tf _ _ _ H3 _ y hy2 hns⟩
  have a4q : A4 tq = List.replicate q true ∧ H4 tq = 0 := by
    rw [hA4, hH4, install_sh P tf _ _ _ i4 A3 _ 0 _ sD0, dockH_sh P tf _ _ _ i4 H3 _ 0 _ sD0]; exact ⟨rfl, rfl⟩
  have a4c : A4 (qc P tf source a k k0 h) = List.replicate q true ∧ H4 (qc P tf source a k k0 h) = 0 := by
    rw [hA4, hH4, qc, install_rg P tf _ _ _ i4 A3 _ _ rfl, dockH_rg P tf _ _ _ i4 H3 _ _ rfl]
    exact ⟨by simp, rfl⟩
  have a4x : A4 (xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H4 (xT P tf) = 0 := by
    have hns : ∀ i b, shD P tf tq i = some b → b ≠ xT P tf := fun i b hi e => by
      obtain ⟨_, u⟩ := shD_some P tf tq i b hi; subst u; rw [e, xT_val] at htq; omega
    rw [hA4, hH4, install_low P tf _ _ _ A3 _ _ (by rw [xT_val]; omega) hns,
      dockH_low P tf _ _ _ H3 _ _ (by rw [xT_val]; omega) hns]
    exact a3x
  -- stage 5: the padded source
  have i5 := slE_inj P tf source a k k0 h td htd
  have hwv := hw_val P tf source a k k0 h
  have hcv := cp_val P tf source a k k0 h
  have hqv := qc_val P tf source a k k0 h
  have hwlo : (hw P tf source a k k0 h).val < 2 + NL P + oC k k0 := by omega
  have hwne : hw P tf source a k k0 h ≠ tq := fun e => by rw [e] at hwlo hwv; omega
  have hcne : cp P tf source a k k0 h ≠ tq := fun e => by rw [e] at hcv; omega
  have hdne : td ≠ tq := fun e => htqd e.symm
  have e4h := lo4 (hw P tf source a k k0 h) (by omega) (by omega) hwne
  have e3h := lo3 (hw P tf source a k k0 h) (by omega) hwlo hwne
  have e4c := lo4 (cp P tf source a k k0 h) (by omega) (by omega) hcne
  have e4d := lo4 td (by omega) (by omega) hdne
  have e3d := lo3 td (by omega) (by omega) hdne
  have e2d := lo2 td (by omega) htd.2
  have e1d := lo1 td (by omega) htd.2
  have d4 : A4 td = PCPPNative.descriptor O ∧ H4 td = 0 := by
    rw [e4d.1, e3d.1, e2d.1, e1d.1, e4d.2, e3d.2, e2d.2, e1d.2]; exact ⟨hdA, hdH⟩
  have h4h : A4 (hw P tf source a k k0 h) = RepairOrdinary.frame (HierarchySourceInput.hierarchyInput Hh ⟨N, x⟩) ∧
      H4 (hw P tf source a k k0 h) = 0 := by
    rw [e4h.1, e3h.1, e4h.2, e3h.2]; exact a2h
  have h4c : A4 (cp P tf source a k k0 h) = List.replicate (FrontCapStage.capOf (List.ofFn x) q) true ∧
      H4 (cp P tf source a k k0 h) = 0 := by
    rw [e4c.1, e4c.2]; exact a3c
  have sEW : shE P tf source a k k0 h td (gWidth source a k) = some (qc P tf source a k k0 h) := by simp [shE]
  have hd := gdist source a k
  have sEH : shE P tf source a k k0 h td (gHier source a k) = some (hw P tf source a k k0 h) := by
    unfold shE; rw [if_neg (fun e => hd.1 (congrArg Fin.val e).symm), if_pos rfl]
  have sED : shE P tf source a k k0 h td (gDesc source a k) = some td := by
    unfold shE
    rw [if_neg (fun e => hd.2.1 (congrArg Fin.val e).symm), if_neg (fun e => hd.2.2.2.1 (congrArg Fin.val e).symm),
      if_pos rfl]
  have sEC : shE P tf source a k k0 h td (gCap source a k) = some (cp P tf source a k k0 h) := by
    unfold shE
    rw [if_neg (fun e => hd.2.2.1 (congrArg Fin.val e).symm), if_neg (fun e => hd.2.2.2.2.1 (congrArg Fin.val e).symm),
      if_neg (fun e => hd.2.2.2.2.2 (congrArg Fin.val e).symm), if_pos rfl]
  have sEN : ∀ j, j ≠ gWidth source a k → j ≠ gHier source a k → j ≠ gDesc source a k → j ≠ gCap source a k →
      shE P tf source a k k0 h td j = none := fun j a1 a2 a3 a4 => by simp [shE, a1, a2, a3, a4]
  obtain ⟨H5, A5, r5, c5A, c5H, c5o⟩ := FrontG3.g3_step source a Hh Cpad hcoeff hpad ⟨N, x⟩ q hq O
    (FrontCapStage.capOf (List.ofFn x) q) hcap _ i5 H4 A4
    (fun j => by
      by_cases jW : j = gWidth source a k
      · subst jW; rw [sl_some P tf _ _ _ _ _ sEW]; exact a4c.2
      · by_cases jH : j = gHier source a k
        · subst jH; rw [sl_some P tf _ _ _ _ _ sEH]; exact h4h.2
        · by_cases jD : j = gDesc source a k
          · subst jD; rw [sl_some P tf _ _ _ _ _ sED]; exact d4.2
          · by_cases jC : j = gCap source a k
            · subst jC; rw [sl_some P tf _ _ _ _ _ sEC]; exact h4c.2
            · rw [sl_none P tf _ _ _ j (sEN j jW jH jD jC)]; exact (pristineH_rg P tf _ _ H4 A4 P4 j).2)
    (fun j => by
      rw [oinputG_val]
      by_cases jW : j = gWidth source a k
      · rw [if_pos jW]; subst jW; rw [sl_some P tf _ _ _ _ _ sEW]; exact a4c.1
      · rw [if_neg jW]
        by_cases jH : j = gHier source a k
        · rw [if_pos jH]; subst jH; rw [sl_some P tf _ _ _ _ _ sEH]; exact h4h.1
        · rw [if_neg jH]
          by_cases jD : j = gDesc source a k
          · rw [if_pos jD]; subst jD; rw [sl_some P tf _ _ _ _ _ sED]; exact d4.1
          · rw [if_neg jD]
            by_cases jC : j = gCap source a k
            · rw [if_pos jC]; subst jC; rw [sl_some P tf _ _ _ _ _ sEC]; exact h4c.1
            · rw [if_neg jC, sl_none P tf _ _ _ j (sEN j jW jH jD jC)]; exact (pristineH_rg P tf _ _ H4 A4 P4 j).1)
  have hlowE : ∀ i b, shE P tf source a k k0 h td i = some b → b.val < 2 + NL P + oG k k0 := fun i b hi => by
    have hO := (FrontHierarchy.hOut k).isLt
    rcases shE_some P tf source a k k0 h td i b hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega
  have notE : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → y ≠ td →
      ∀ j, sl P tf (shE P tf source a k k0 h td) (oG k k0) (hE tf source a k k0 h) j ≠ y := fun y hy hyd j e => by
    unfold sl at e
    cases hj : shE P tf source a k k0 h td j with
    | none =>
      rw [hj] at e; simp only [Option.getD_none] at e
      have := congrArg Fin.val e; rw [rg_val] at this; omega
    | some b =>
      rw [hj] at e; simp only [Option.getD_some] at e
      have hO := (FrontHierarchy.hOut k).isLt
      rcases shE_some P tf source a k k0 h td j b hj with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩
      · rw [e] at u; omega
      · rw [e] at u; omega
      · exact hyd (e.symm.trans (Fin.ext u))
      · rw [e] at u; omega
  have kE : oG k k0 + gtapes source a k = k0 + PH2 source a k := by unfold PH2; omega
  refine ⟨H5, A5, Step.seq r1 (Step.seq r2 (Step.seq r3 (Step.seq r4 r5))), ⟨fun y hy => ?_, fun i => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have hn : ∀ j, sl P tf (shE P tf source a k k0 h td) (oG k k0) (hE tf source a k k0 h) j ≠ y := by
      intro j e
      have hl := sl_lt P tf (shE P tf source a k k0 h td) (oG k k0) (hE tf source a k k0 h) hlowE j
      rw [e] at hl
      omega
    rw [(c5o y hn).1, (c5o y hn).2]
    exact P4.1 y (by omega)
  · have hn := not_slot_lp P tf _ _ (hE tf source a k k0 h) (fun i b hi => by
      have hO := (FrontHierarchy.hOut k).isLt
      rcases shE_some P tf source a k k0 h td i b hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega) i
    rw [(c5o _ hn).1, (c5o _ hn).2]
    exact P4.2 i
  · refine ⟨?_, ?_⟩
    · rw [poT, c5A 0, clauseData_zero]
    · rw [poT, c5H 0, heads_zero]
  · have hn := notE (xT P tf) (by rw [xT_val]; omega) (fun e => by rw [← e, xT_val] at htd; omega)
    rw [(c5o _ hn).1, (c5o _ hn).2]; exact a4x
  · have hn := notE tq htq.2 htqd
    rw [(c5o _ hn).1, (c5o _ hn).2]; exact a4q
  · intro y hy1 hy2 hyd
    have hn := notE y hy2 hyd
    rw [(c5o _ hn).1, (c5o _ hn).2]
    by_cases hyq : y = tq
    · subst hyq; rw [a4q.1, a4q.2, hqA, hqH]; exact ⟨rfl, rfl⟩
    · have e4 := lo4 y hy1 (by omega) hyq
      have e3 := lo3 y hy1 (by omega) hyq
      have e2 := lo2 y hy1 hy2
      have e1 := lo1 y hy1 hy2
      exact ⟨by rw [e4.1, e3.1, e2.1, e1.1], by rw [e4.2, e3.2, e2.2, e1.2]⟩

end Ph

end NearCubicWires.WireExponent3_5.UnionMachine.FrontPh2
