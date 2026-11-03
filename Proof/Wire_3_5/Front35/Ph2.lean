import Proof.Wire_3_5.Front35.ColdDock
import Proof.Wire_3_5.Front35.Walk
import Proof.Wire_3_5.UnionMachine.FrontPh2

/-!
# The front's phase 2 at the outer step: the cold front end on the guessed pair

Paper v2, §H.5, the outer step of the weak machine (the source check, the description-length guard, the A-run on
`⟨Γ_src⟩_a`, the substitution `H_Γ`) and "Systematic parities are constructed from the PCPP output": after phase 1 (the
copy of `x`, the width `1^q`, the old oracle stage), on three regions:
1. the walk stage (`Walk.walk_ready`) on the witness: the pair field's payload `frame raw`, `raw = payload w.tail`;
2. a copy of `frame x` (base `RecoveryColdWitnessCopy`);
3. the cold front end (`ColdNativeW`, docked by `cold_step`) on the copy and the payload: the verdict `Passes` on its
   flag tape and, on a pass, the PCPP output word of the request of `H_Γ` at head `0`.
**`ph2_step`**: the run, the flag, the PCPP word; `x` kept; every front tape below the regions untouched; the front's
tapes past the regions blank.

Paper quantity of the main statement: the verdict of the outer step's guards and the PCPP output of `H_Γ` (`Outer.Dat`).
-/

set_option autoImplicit false

namespace NearCubicWires.WireExponent3_5.UnionMachine.Front35.Ph2

open _root_.NearCubicWires _root_.NearCubicWires.LocalBitMultitape _root_.NearCubicWires.RepairOrdinary
open _root_.NearCubicWires.RepairRepresentation _root_.NearCubicWires.RepairSource _root_.NearCubicWires.ExtDecompositionBatch
open _root_.NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open _root_.NearCubicWires.WireExponent3_5 _root_.NearCubicWires.WireExponent3_5.Cost
open _root_.NearCubicWires.WireExponent3_5.UnionMachine _root_.NearCubicWires.WireExponent3_5.UnionMachine.Plan
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontPh1 (xT xT_val wT wT_val copy_in)
open _root_.NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf ones ones_le)
open NearCubicGates.Close W3.NearCubicWires.RepairSource.Outer3

section Ph
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  {mw : Outer.MWSource} {k : ℕ} {H : OrdinaryHierarchy (fun n => n ^ (k + 2))} {L : ℕ}
  {SV : Outer.SuccinctVerifier H L} {a : PointwisePCPPAlgorithm} {cutoff D degree copies : ℕ} {delta : ℚ}
  (C : ColdNativeW mw SV a cutoff D degree copies delta) (k0 : ℕ)

/-- The phase's size: the walk stage, the copy of `x`, the cold front end. -/
abbrev PH2 : ℕ := FrontOracle.OS + 4 + C.tapes

/-- The copy's and the cold front end's region offsets. -/
abbrev oA : ℕ := k0 + FrontOracle.OS
abbrev oK : ℕ := k0 + FrontOracle.OS + 4

theorem hW (h : k0 + PH2 C ≤ tf) : k0 + FrontOracle.OS ≤ tf := by unfold PH2 at h; omega
theorem hA (h : k0 + PH2 C ≤ tf) : oA k0 + 4 ≤ tf := by unfold PH2 at h; unfold oA; omega
theorem hK (h : k0 + PH2 C ≤ tf) : oK k0 + C.tapes ≤ tf := by unfold PH2 at h; unfold oK; omega

variable (h : k0 + PH2 C ≤ tf)

/-- The walk stage's payload tape (its tape `12`). -/
noncomputable def td : Fin (NW P tf) := rg P tf k0 (hW tf C k0 h) (12 : Fin FrontOracle.OS)

theorem td_val : (td P tf C k0 h).val = 2 + NL P + (k0 + 12) := rfl

/-- The copy of `x`. -/
noncomputable def cx : Fin (NW P tf) := rg P tf (oA k0) (hA tf C k0 h) (1 : Fin 4)

theorem cx_val : (cx P tf C k0 h).val = 2 + NL P + (k0 + FrontOracle.OS + 1) := rfl

/-- The walk stage's shared tape: its witness tape `1` on the front's witness tape. -/
noncomputable def shW (j : Fin FrontOracle.OS) : Option (Fin (NW P tf)) := if j.val = 1 then some (wT P tf) else none

theorem shW_some (j : Fin FrontOracle.OS) (b : Fin (NW P tf)) (hj : shW P tf j = some b) : j.val = 1 ∧ b.val = 1 := by
  unfold shW at hj; split_ifs at hj with a0; cases hj; exact ⟨a0, rfl⟩

/-- The cold front end's shared tapes: its input tape `2` on the copy of `x`, its raw-field tape on the payload tape. -/
noncomputable def shK (j : Fin C.tapes) : Option (Fin (NW P tf)) :=
  if j.val = 2 then some (cx P tf C k0 h) else if j.val = C.oracleIndex then some (td P tf C k0 h) else none

theorem shK_some (j : Fin C.tapes) (b : Fin (NW P tf)) (hj : shK P tf C k0 h j = some b) :
    (j.val = 2 ∧ b = cx P tf C k0 h) ∨ (j.val = C.oracleIndex ∧ b = td P tf C k0 h) := by
  unfold shK at hj
  split_ifs at hj with a0 a1 <;> cases hj
  · exact Or.inl ⟨a0, rfl⟩
  · exact Or.inr ⟨a1, rfl⟩

/-- The slots of the walk stage, the copy and the cold front end. -/
noncomputable abbrev slW := sl P tf (shW P tf) k0 (hW tf C k0 h)
noncomputable abbrev slA := sl P tf (FrontPh2.shA P tf) (oA k0) (hA tf C k0 h)
noncomputable abbrev slK := sl P tf (shK P tf C k0 h) (oK k0) (hK tf C k0 h)

theorem slW_inj : Function.Injective (slW P tf C k0 h) := by
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (fun i b hi => ?_)
  · have := shW_some P tf i b hi; have := shW_some P tf j b hj; exact Fin.ext (by omega)
  · have := shW_some P tf i b hi; omega

theorem slA_inj : Function.Injective (slA P tf C k0 h) := by
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (fun i b hi => ?_)
  · have := FrontPh2.shA_some P tf i b hi; have := FrontPh2.shA_some P tf j b hj; exact Fin.ext (by omega)
  · have := FrontPh2.shA_some P tf i b hi; omega

theorem shK_low (i : Fin C.tapes) (b : Fin (NW P tf))
    (hi : shK P tf C k0 h i = some b) : b.val < 2 + NL P + oK k0 := by
  rcases shK_some P tf C k0 h i b hi with ⟨_, u⟩ | ⟨_, u⟩ <;> subst u
  · rw [cx_val]; unfold oK; omega
  · rw [td_val]; unfold oK; have : 12 < FrontOracle.OS := by decide
    omega

theorem slK_inj : Function.Injective (slK P tf C k0 h) := by
  have h2 := C.two_lt
  have hOS : 12 < FrontOracle.OS := by decide
  refine sl_inj P tf _ _ _ (fun i j b hi hj => ?_) (shK_low P tf C k0 h)
  rcases shK_some P tf C k0 h i b hi with ⟨u1, u2⟩ | ⟨u1, u2⟩ <;>
    rcases shK_some P tf C k0 h j b hj with ⟨v1, v2⟩ | ⟨v1, v2⟩
  · exact Fin.ext (by omega)
  · exfalso; rw [u2] at v2; have := congrArg Fin.val v2; rw [cx_val, td_val] at this; omega
  · exfalso; rw [u2] at v2; have := congrArg Fin.val v2; rw [cx_val, td_val] at this; omega
  · exact Fin.ext (by omega)

/-- **Phase 2**: the walk stage, the copy of `x`, the cold front end. -/
noncomputable def ph2M :=
  Composition.machine (RecoveryFocus.machine (slW P tf C k0 h) Walk.wkMachine)
  (Composition.machine (RecoveryFocus.machine (slA P tf C k0 h) RecoveryColdWitnessCopy.machine)
    (RecoveryFocus.machine (slK P tf C k0 h) C.machine))

/-- The flag tape (the verdict `Passes`). -/
noncomputable def flT : Fin (NW P tf) := slK P tf C k0 h C.flagSlot

/-- The PCPP output word's tape (cache slot `0`). -/
noncomputable def poT : Fin (NW P tf) := slK P tf C k0 h (C.cacheSlots 0)

/-- **Phase 2's run.** -/
theorem ph2_step {N : ℕ} (x : BitInput N) (w : List Bool) (h16 : 16 * w.length ≤ N)
    (Ha : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool) (hP : PristineH P tf Ha A k0)
    (hx : A (xT P tf) = RepairOrdinary.frame (List.ofFn x)) (hxH : Ha (xT P tf) = 0)
    (hw : A (wT P tf) = RepairOrdinary.frame w) (hwH : Ha (wT P tf) = 0) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (ph2M P tf C k0 h) (Walk.wkCost w + 1 + ((8 * (List.ofFn x).length + 14) + 1 +
        C.budget N x (payload w.tail))) Ha A H' A' ∧
      PristineH P tf H' A' (k0 + PH2 C) ∧
      H' (flT P tf C k0 h) = 0 ∧
      readTapeBit (A' (flT P tf C k0 h)) 0 = C.passed (List.ofFn x) (payload w.tail) ∧
      (C.passed (List.ofFn x) (payload w.tail) = true → ∀ B : Outer.OuterGuess (Outer.width mw SV N),
        Worker.Decodes (Outer.width mw SV N) (payload w.tail) B →
        let r := requestAt mw SV a (Nat.log 2 N) B
        A' (poT P tf C k0 h) = pcppOutput r (a.output r) ∧ H' (poT P tf C k0 h) = 0) ∧
      ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → A' y = A y ∧ H' y = Ha y := by
  have h2 := C.two_lt
  have hoi := C.oracle_lt
  have hOS : 12 < FrontOracle.OS := by decide
  have hraw : 16 * (payload w.tail).length ≤ N := by
    have := List.length_take_le (ones w.tail) (w.tail.drop (ones w.tail + 1))
    have h3 := ones_le w.tail
    have h4 : (payload w.tail).length ≤ w.length := by simp [payload] at this ⊢
    omega
  -- stage 1: the walk stage
  obtain ⟨o1, g1, o14, o13, o12, o11, o1w⟩ := Walk.walk_ready w
  have i1 := slW_inj P tf C k0 h
  have hlow1 : ∀ i b, shW P tf i = some b → b.val < 2 + NL P + k0 := fun i b hi => by
    have := shW_some P tf i b hi; omega
  have hL1 : ∀ i b, shW P tf i = some b → 2 + NL P ≤ b.val ∨ b.val < 2 := fun i b hi => by
    have := shW_some P tf i b hi; omega
  have sW1 : shW P tf (1 : Fin FrontOracle.OS) = some (wT P tf) := rfl
  have r1 := dockAnyR g1 _ i1 Ha A
    (fun j => by
      dsimp only [slW]
      by_cases hj : j.val = 1
      · rw [show j = 1 from Fin.ext hj, sl_some P tf _ k0 _ 1 _ sW1]; exact hwH
      · rw [sl_none P tf _ k0 _ j (by simp [shW, hj])]; exact (pristineH_rg P tf k0 _ Ha A hP j).2)
    (fun j => by
      dsimp only [slW]
      unfold Walk.wkIn
      by_cases hj : j.val = 1
      · rw [if_pos hj, show j = 1 from Fin.ext hj, sl_some P tf _ k0 _ 1 _ sW1]; exact hw
      · rw [if_neg hj, sl_none P tf _ k0 _ j (by simp [shW, hj])]; exact (pristineH_rg P tf k0 _ Ha A hP j).1)
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = dockH (slW P tf C k0 h) Ha (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = install (slW P tf C k0 h) A o1 := ⟨_, rfl⟩
  rw [← hH1, ← hA1] at r1
  have P1 : PristineH P tf H1 A1 (k0 + FrontOracle.OS) := by
    rw [hH1, hA1]; exact pristineH_after P tf _ k0 _ hlow1 hL1 Ha A _ _ hP
  have lo1 : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → y ≠ wT P tf → A1 y = A y ∧ H1 y = Ha y := by
    intro y hy hyw
    have hn : ∀ j, slW P tf C k0 h j ≠ y := fun j e => by
      dsimp only [slW] at e
      unfold sl at e
      cases hj : shW P tf j with
      | none =>
        rw [hj] at e; simp only [Option.getD_none] at e
        have := congrArg Fin.val e; rw [rg_val] at this; omega
      | some b =>
        rw [hj] at e; simp only [Option.getD_some] at e
        have := shW_some P tf j b hj
        exact hyw (by rw [← e]; exact Fin.ext (by rw [wT_val]; exact this.2))
    rw [hA1, hH1, install_other _ _ _ _ hn, dockH_other _ _ _ _ hn]
    exact ⟨rfl, rfl⟩
  have a1w : A1 (wT P tf) = RepairOrdinary.frame w ∧ H1 (wT P tf) = 0 := by
    rw [hA1, hH1, install_sh P tf _ k0 _ i1 A _ 1 _ sW1, dockH_sh P tf _ k0 _ i1 Ha _ 1 _ sW1]; exact ⟨o1w, rfl⟩
  have a1d : A1 (td P tf C k0 h) = RepairOrdinary.frame (payload w.tail) ∧ H1 (td P tf C k0 h) = 0 := by
    rw [hA1, hH1, td, install_rg P tf _ k0 _ i1 A _ 12 rfl, dockH_rg P tf _ k0 _ i1 Ha _ 12 rfl]
    exact ⟨o12, rfl⟩
  have a1x : A1 (xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H1 (xT P tf) = 0 := by
    obtain ⟨e1, e2⟩ := lo1 (xT P tf) (by rw [xT_val]; omega) (fun e => by
      have := congrArg Fin.val e; rw [xT_val, wT_val] at this; omega)
    rw [e1, e2]; exact ⟨hx, hxH⟩
  -- stage 2: the copy of `x`
  have i2 := slA_inj P tf C k0 h
  have hlow2 : ∀ i b, FrontPh2.shA P tf i = some b → b.val < 2 + NL P + oA k0 := fun i b hi => by
    have := FrontPh2.shA_some P tf i b hi; omega
  have hL2 : ∀ i b, FrontPh2.shA P tf i = some b → 2 + NL P ≤ b.val ∨ b.val < 2 := fun i b hi => by
    have := FrontPh2.shA_some P tf i b hi; omega
  have sA0 : FrontPh2.shA P tf (0 : Fin 4) = some (xT P tf) := rfl
  have r2 := dockAny (FrontLoopKit.step_of_rready (RecoveryColdWitnessCopy.copy_ready (List.ofFn x))) _ i2 H1 A1
    (fun j => by
      dsimp only [slA]
      by_cases hj : j.val = 0
      · rw [show j = 0 from Fin.ext hj, sl_some P tf _ _ _ 0 _ sA0]; exact a1x.2
      · rw [sl_none P tf _ _ _ j (by simp [FrontPh2.shA, hj])]; exact (pristineH_rg P tf _ _ H1 A1 P1 j).2)
    (fun j => by
      dsimp only [slA]
      rw [copy_in]
      by_cases hj : j.val = 0
      · rw [if_pos hj, show j = 0 from Fin.ext hj, sl_some P tf _ _ _ 0 _ sA0]; exact a1x.1
      · rw [if_neg hj, sl_none P tf _ _ _ j (by simp [FrontPh2.shA, hj])]; exact (pristineH_rg P tf _ _ H1 A1 P1 j).1)
  obtain ⟨H2, hH2⟩ : ∃ H2, H2 = dockH (slA P tf C k0 h) H1 (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = install (slA P tf C k0 h) A1 (RecoveryColdWitnessCopy.output (List.ofFn x)) :=
    ⟨_, rfl⟩
  rw [← hH2, ← hA2] at r2
  have P2 : PristineH P tf H2 A2 (oA k0 + 4) := by
    rw [hH2, hA2]; exact pristineH_after P tf _ _ _ hlow2 hL2 H1 A1 _ _ P1
  have lo2 : ∀ y : Fin (NW P tf), y ≠ xT P tf → y.val < 2 + NL P + oA k0 → A2 y = A1 y ∧ H2 y = H1 y := by
    intro y hy1 hy2
    have hns : ∀ i b, FrontPh2.shA P tf i = some b → b ≠ y := fun i b hi e => by
      unfold FrontPh2.shA at hi; split_ifs at hi; cases hi; exact hy1 e.symm
    rw [hA2, hH2]
    exact ⟨install_low P tf _ _ _ A1 _ y hy2 hns, dockH_low P tf _ _ _ H1 _ y hy2 hns⟩
  have a2x : A2 (xT P tf) = RepairOrdinary.frame (List.ofFn x) ∧ H2 (xT P tf) = 0 := by
    rw [hA2, hH2, install_sh P tf _ _ _ i2 A1 _ 0 _ sA0, dockH_sh P tf _ _ _ i2 H1 _ 0 _ sA0]; exact ⟨rfl, rfl⟩
  have a2c : A2 (cx P tf C k0 h) = RepairOrdinary.frame (List.ofFn x) ∧ H2 (cx P tf C k0 h) = 0 := by
    rw [hA2, hH2, cx, install_rg P tf _ _ _ i2 A1 _ 1 rfl, dockH_rg P tf _ _ _ i2 H1 _ 1 rfl]
    exact ⟨rfl, rfl⟩
  have a2d : A2 (td P tf C k0 h) = RepairOrdinary.frame (payload w.tail) ∧ H2 (td P tf C k0 h) = 0 := by
    obtain ⟨e1, e2⟩ := lo2 (td P tf C k0 h) (fun e => by have := congrArg Fin.val e; rw [td_val, xT_val] at this; omega)
      (by rw [td_val]; unfold oA; omega)
    rw [e1, e2]; exact a1d
  -- stage 3: the cold front end
  have i3 := slK_inj P tf C k0 h
  have sK2 : ∀ j : Fin C.tapes, j.val = 2 → shK P tf C k0 h j = some (cx P tf C k0 h) := fun j hj => by
    simp [shK, hj]
  have sKO : ∀ j : Fin C.tapes, j.val = C.oracleIndex → shK P tf C k0 h j = some (td P tf C k0 h) := fun j hj => by
    simp [shK, hj, show C.oracleIndex ≠ 2 by omega]
  have sKN : ∀ j : Fin C.tapes, j.val ≠ 2 → j.val ≠ C.oracleIndex → shK P tf C k0 h j = none := fun j a1 a2 => by
    simp [shK, a1, a2]
  obtain ⟨H3, A3, r3, f3H, f3A, c3, o3⟩ := cold_step mw SV a cutoff D degree copies delta C x (payload w.tail) hraw _
    i3 H2 A2
    (fun j => by
      dsimp only [slK]
      by_cases j2 : j.val = 2
      · rw [sl_some P tf _ _ _ j _ (sK2 j j2)]; exact a2c.2
      · by_cases jO : j.val = C.oracleIndex
        · rw [sl_some P tf _ _ _ j _ (sKO j jO)]; exact a2d.2
        · rw [sl_none P tf _ _ _ j (sKN j j2 jO)]; exact (pristineH_rg P tf _ _ H2 A2 P2 j).2)
    (fun j => by
      dsimp only [slK]
      rw [C.input_eq]
      by_cases jO : j.val = C.oracleIndex
      · rw [if_pos jO, sl_some P tf _ _ _ j _ (sKO j jO)]; exact a2d.1
      · rw [if_neg jO]
        by_cases j2 : j.val = 2
        · rw [if_pos j2, sl_some P tf _ _ _ j _ (sK2 j j2)]; exact a2c.1
        · rw [if_neg j2, sl_none P tf _ _ _ j (sKN j j2 jO)]; exact (pristineH_rg P tf _ _ H2 A2 P2 j).1)
  have hlowK := shK_low P tf C k0 h
  have notK : ∀ y : Fin (NW P tf), y.val < 2 + NL P + k0 → ∀ j, slK P tf C k0 h j ≠ y :=
    fun y hy j e => by
      dsimp only [slK] at e
      unfold sl at e
      cases hj : shK P tf C k0 h j with
      | none =>
        rw [hj] at e; simp only [Option.getD_none] at e
        have := congrArg Fin.val e; rw [rg_val] at this; unfold oK at this; omega
      | some b =>
        rw [hj] at e; simp only [Option.getD_some] at e
        rcases shK_some P tf C k0 h j b hj with ⟨_, u⟩ | ⟨_, u⟩ <;> subst u
        · have := congrArg Fin.val e; rw [cx_val] at this; omega
        · have := congrArg Fin.val e; rw [td_val] at this; omega
  refine ⟨H3, A3, Step.seq r1 (Step.seq r2 r3), ⟨fun y hy => ?_, fun i => ?_⟩, f3H, f3A, ?_, ?_⟩
  · have hn : ∀ j, slK P tf C k0 h j ≠ y := by
      intro j e
      have hl := sl_lt P tf (shK P tf C k0 h) (oK k0) (hK tf C k0 h) hlowK j
      change (slK P tf C k0 h j).val < _ at hl
      rw [e] at hl
      unfold oK PH2 at *
      omega
    rw [(o3 y hn).1, (o3 y hn).2]
    exact P2.1 y (by unfold PH2 at hy; unfold oA; omega)
  · have hn := not_slot_lp P tf _ _ (hK tf C k0 h) (fun i b hi => by
      rcases shK_some P tf C k0 h i b hi with ⟨_, u⟩ | ⟨_, u⟩ <;> subst u
      · left; rw [cx_val]; omega
      · left; rw [td_val]; omega) i
    rw [(o3 _ hn).1, (o3 _ hn).2]
    exact P2.2 i
  · intro hp B hB
    obtain ⟨c1, c2⟩ := c3 hp B hB
    exact ⟨by rw [poT, c1 0, FrontPh2.clauseData_zero], by rw [poT, c2 0, FrontPh2.heads_zero]⟩
  · intro y hy
    have hn := notK y hy
    rw [(o3 _ hn).1, (o3 _ hn).2]
    by_cases hyx : y = xT P tf
    · subst hyx; rw [a2x.1, a2x.2, hx, hxH]; exact ⟨rfl, rfl⟩
    · obtain ⟨e1, e2⟩ := lo2 y hyx (by unfold oA; omega)
      rw [e1, e2]
      by_cases hyw : y = wT P tf
      · subst hyw; rw [a1w.1, a1w.2, hw, hwH]; exact ⟨rfl, rfl⟩
      · exact lo1 y hy hyw

end Ph

end NearCubicWires.WireExponent3_5.UnionMachine.Front35.Ph2
