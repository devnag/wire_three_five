import Proof.Wire_3_5.UnionMachine.FrontSlots
import Proof.Wire_3_5.UnionMachine.FrontWidthCost
import Proof.Wire_3_5.UnionMachine.FrontOracle
import Proof.Wire_3_5.UnionMachine.FrontSizeStage
import Proof.Amplification.RecoveryWitnessCopy

/-! # C6 front, the chain, phase 1: the width, the oracle field, the oracle's size (P3:3637-3640, 3669-3671)

From the refuter's framed input `x` (tape `0`) and witness `w` (tape `1`), on four regions of the front's tapes:
1. a copy of `frame x` (base's `RecoveryColdWitnessCopy`);
2. the native width `1^q`, `q = q(N)` (`FrontWidthCost.qMachine_ready_c`, on the copy);
3. the oracle stage (`FrontOracle.oracle_ready`: tag, walker verdict, rest, decoder flag and descriptor), sharing
   `x`, `w` and `1^q`;
4. the size stage (`FrontSizeStage.size_ready`: the size verdict), sharing `x`, the flag, the descriptor, `1^q`.
**`ph1_step`**: the run and every output, at heads `0`; everything below the regions but `x`, `w` untouched; the
front's tapes past the regions still blank.

Paper quantity: `q(N)`, the guess's tag, oracle and rest, and the oracle's size test (P3:3637-3640, 3669). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontPh1
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.RepairOrdinary.RadixSemantics (value)
open NearCubicWires.WireExponent3_5.UnionMachine.FrontWalkRef (payload restOf)

section Ph
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  (k Ap G k0 : ℕ)

/-- The refuter's input and witness tapes. -/
noncomputable def xT : Fin (NW P tf) := ⟨0, by show 0 < 2 + NL P + tf; omega⟩
noncomputable def wT : Fin (NW P tf) := ⟨1, by show 1 < 2 + NL P + tf; omega⟩

/-- The phase's size. -/
noncomputable abbrev PH1 (k : ℕ) : ℕ := 4 + FrontWidth.QT k + FrontOracle.OS + FrontSizeStage.ST

theorem h1 (k k0 tf : ℕ) (h : k0 + PH1 k ≤ tf) : k0 + 4 ≤ tf := by unfold PH1 at h; omega
theorem h2 (k k0 tf : ℕ) (h : k0 + PH1 k ≤ tf) : k0 + 4 + FrontWidth.QT k ≤ tf := by unfold PH1 at h; omega
theorem h3 (k k0 tf : ℕ) (h : k0 + PH1 k ≤ tf) : k0 + 4 + FrontWidth.QT k + FrontOracle.OS ≤ tf := by
  unfold PH1 at h; omega
theorem h4 (k k0 tf : ℕ) (h : k0 + PH1 k ≤ tf) :
    k0 + 4 + FrontWidth.QT k + FrontOracle.OS + FrontSizeStage.ST ≤ tf := by unfold PH1 at h; omega

variable (h : k0 + PH1 k ≤ tf)

/-- The copy of `frame x`. -/
noncomputable def cxT : Fin (NW P tf) := rg P tf k0 (h1 k k0 tf h) (1 : Fin 4)
/-- `1^q`. -/
noncomputable def qT : Fin (NW P tf) := rg P tf (k0 + 4) (h2 k k0 tf h) (FrontWidth.qOut k)
/-- The oracle stage's outputs. -/
noncomputable def orT (j : Fin FrontOracle.OS) : Fin (NW P tf) := rg P tf (k0 + 4 + FrontWidth.QT k) (h3 k k0 tf h) j
/-- The size verdict. -/
noncomputable def vT : Fin (NW P tf) :=
  rg P tf (k0 + 4 + FrontWidth.QT k + FrontOracle.OS) (h4 k k0 tf h) (12 : Fin FrontSizeStage.ST)

/-! ## The shared tapes -/

noncomputable def sh1 (j : Fin 4) : Option (Fin (NW P tf)) := if j.val = 0 then some (xT P tf) else none
noncomputable def sh2 (j : Fin (FrontWidth.QT k)) : Option (Fin (NW P tf)) :=
  if j = FrontWidth.inT k then some (cxT P tf k k0 h) else none
noncomputable def sh3 (j : Fin FrontOracle.OS) : Option (Fin (NW P tf)) :=
  if j.val = 0 then some (xT P tf) else if j.val = 1 then some (wT P tf) else if j.val = 2 then some (qT P tf k k0 h)
  else none
noncomputable def sh4 (j : Fin FrontSizeStage.ST) : Option (Fin (NW P tf)) :=
  if j.val = 0 then some (xT P tf) else if j.val = 1 then some (orT P tf k k0 h FrontOracle.flagO)
  else if j.val = 2 then some (orT P tf k k0 h FrontOracle.descO) else if j.val = 3 then some (qT P tf k k0 h)
  else none

theorem xT_val : (xT P tf).val = 0 := rfl
theorem wT_val : (wT P tf).val = 1 := rfl

/-! ## Injectivity -/

theorem qOut_ne_inT : FrontWidth.qOut k ≠ FrontWidth.inT k := by
  intro e
  have h1 := congrArg Fin.val e
  have h2 := FrontWidth.tsl_ge k 26
  have h3 := (FrontWidth.inT k).isLt
  unfold FrontWidth.inT at h1
  rw [FrontWidth.hs_val] at h1
  have h4 := (HierarchyFromInput.field (k + 2) 2).isLt
  unfold FrontWidth.qOut at h1
  omega

theorem flag_ne : FrontOracle.flagO ≠ FrontOracle.descO := by decide
theorem flag_val : 3 ≤ FrontOracle.flagO.val ∧ FrontOracle.flagO.val ≠ 11 ∧ FrontOracle.flagO.val ≠ 13 ∧
    FrontOracle.flagO.val ≠ 14 := by decide
theorem desc_val : 3 ≤ FrontOracle.descO.val ∧ FrontOracle.descO.val ≠ 11 ∧ FrontOracle.descO.val ≠ 13 ∧
    FrontOracle.descO.val ≠ 14 := by decide

theorem sl1_inj : Function.Injective (sl P tf (sh1 P tf) k0 (h1 k k0 tf h)) := by
  refine sl_inj P tf _ k0 _ (fun i j a hi hj => ?_) (fun i a hi => ?_)
  · unfold sh1 at hi hj
    split_ifs at hi hj with a1 a2
    exact Fin.ext (by omega)
  · unfold sh1 at hi
    split_ifs at hi
    cases hi
    rw [xT_val]; omega

theorem sl2_inj : Function.Injective (sl P tf (sh2 P tf k k0 h) (k0 + 4) (h2 k k0 tf h)) := by
  refine sl_inj P tf _ (k0 + 4) _ (fun i j a hi hj => ?_) (fun i a hi => ?_)
  · unfold sh2 at hi hj
    split_ifs at hi hj with a1 a2
    exact a1.trans a2.symm
  · unfold sh2 at hi
    split_ifs at hi
    cases hi
    simp only [cxT, rg_val, Fin.val_one]
    omega

theorem qT_val : (qT P tf k k0 h).val = 2 + NL P + (k0 + 4 + (FrontWidth.qOut k).val) := by
  simp only [qT, rg_val]

theorem orT_val (j : Fin FrontOracle.OS) : (orT P tf k k0 h j).val = 2 + NL P + (k0 + 4 + FrontWidth.QT k + j.val) :=
  rg_val P tf _ _ j

theorem sh3_some (j : Fin FrontOracle.OS) (a : Fin (NW P tf)) (hj : sh3 P tf k k0 h j = some a) :
    (j.val = 0 ∧ a.val = 0) ∨ (j.val = 1 ∧ a.val = 1) ∨
      (j.val = 2 ∧ a.val = 2 + NL P + (k0 + 4 + (FrontWidth.qOut k).val)) := by
  unfold sh3 at hj
  split_ifs at hj with a0 a1 a2 <;> cases hj
  · exact Or.inl ⟨a0, rfl⟩
  · exact Or.inr (Or.inl ⟨a1, rfl⟩)
  · exact Or.inr (Or.inr ⟨a2, qT_val P tf k k0 h⟩)

theorem sl3_inj : Function.Injective (sl P tf (sh3 P tf k k0 h) (k0 + 4 + FrontWidth.QT k) (h3 k k0 tf h)) := by
  have hq := (FrontWidth.qOut k).isLt
  refine sl_inj P tf _ _ _ (fun i j a hi hj => ?_) (fun i a hi => ?_)
  · apply Fin.ext
    rcases sh3_some P tf k k0 h i a hi with ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ <;>
    rcases sh3_some P tf k k0 h j a hj with ⟨v1, v2⟩ | ⟨v1, v2⟩ | ⟨v1, v2⟩ <;> omega
  · rcases sh3_some P tf k k0 h i a hi with ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> omega

theorem sh4_some (j : Fin FrontSizeStage.ST) (a : Fin (NW P tf)) (hj : sh4 P tf k k0 h j = some a) :
    (j.val = 0 ∧ a.val = 0) ∨ (j.val = 1 ∧ a.val = 2 + NL P + (k0 + 4 + FrontWidth.QT k + FrontOracle.flagO.val)) ∨
      (j.val = 2 ∧ a.val = 2 + NL P + (k0 + 4 + FrontWidth.QT k + FrontOracle.descO.val)) ∨
      (j.val = 3 ∧ a.val = 2 + NL P + (k0 + 4 + (FrontWidth.qOut k).val)) := by
  unfold sh4 at hj
  split_ifs at hj with a0 a1 a2 a3 <;> cases hj
  · exact Or.inl ⟨a0, rfl⟩
  · exact Or.inr (Or.inl ⟨a1, orT_val P tf k k0 h _⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨a2, orT_val P tf k k0 h _⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨a3, qT_val P tf k k0 h⟩))

theorem sl4_inj : Function.Injective
    (sl P tf (sh4 P tf k k0 h) (k0 + 4 + FrontWidth.QT k + FrontOracle.OS) (h4 k k0 tf h)) := by
  have hq := (FrontWidth.qOut k).isLt
  have hf := FrontOracle.flagO.isLt
  have hd := FrontOracle.descO.isLt
  have hfd : FrontOracle.flagO.val ≠ FrontOracle.descO.val := fun e => flag_ne (Fin.ext e)
  refine sl_inj P tf _ _ _ (fun i j a hi hj => ?_) (fun i a hi => ?_)
  · apply Fin.ext
    rcases sh4_some P tf k k0 h i a hi with ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ <;>
    rcases sh4_some P tf k k0 h j a hj with ⟨v1, v2⟩ | ⟨v1, v2⟩ | ⟨v1, v2⟩ | ⟨v1, v2⟩ <;> omega
  · rcases sh4_some P tf k k0 h i a hi with ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ | ⟨u1, u2⟩ <;> omega

/-! ## The phase's machine -/

/-- **Phase 1**: copy `x`, the width, the oracle stage, the size stage. -/
noncomputable def ph1M :=
  Composition.machine (RecoveryFocus.machine (sl P tf (sh1 P tf) k0 (h1 k k0 tf h)) RecoveryColdWitnessCopy.machine)
    (Composition.machine (RecoveryFocus.machine (sl P tf (sh2 P tf k k0 h) (k0 + 4) (h2 k k0 tf h))
      (FrontWidth.qMachine k Ap))
    (Composition.machine (RecoveryFocus.machine (sl P tf (sh3 P tf k k0 h) (k0 + 4 + FrontWidth.QT k) (h3 k k0 tf h))
      FrontOracle.osMachine)
    (RecoveryFocus.machine (sl P tf (sh4 P tf k k0 h) (k0 + 4 + FrontWidth.QT k + FrontOracle.OS) (h4 k k0 tf h))
      (FrontSizeStage.ssMachine (2 ^ RecoveryScheduleEnvelope.oracleDepth G)))))

/-! ## The run -/

theorem copy_in (xs : List Bool) (j : Fin 4) :
    RecoveryColdWitnessCopy.input xs j = if j.val = 0 then RepairOrdinary.frame xs else [] := by
  fin_cases j <;> rfl

theorem sh1_some0 : sh1 P tf (0 : Fin 4) = some (xT P tf) := rfl
theorem sh1_none (j : Fin 4) (hj : j.val ≠ 0) : sh1 P tf j = none := by simp [sh1, hj]
theorem sh2_none (j : Fin (FrontWidth.QT k)) (hj : j ≠ FrontWidth.inT k) : sh2 P tf k k0 h j = none := by
  simp [sh2, hj]
theorem sh3_none (j : Fin FrontOracle.OS) (hj : 3 ≤ j.val) : sh3 P tf k k0 h j = none := by
  simp only [sh3]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
theorem sh4_none (j : Fin FrontSizeStage.ST) (hj : 4 ≤ j.val) : sh4 P tf k k0 h j = none := by
  simp only [sh4]; rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- The size stage shares no oracle output but the flag and the descriptor. -/
theorem sh4_ne_orT (j : Fin FrontOracle.OS) (hjf : j.val ≠ FrontOracle.flagO.val) (hjd : j.val ≠ FrontOracle.descO.val) :
    ∀ i a, sh4 P tf k k0 h i = some a → a ≠ orT P tf k k0 h j := fun i a hi e => by
  have hq := (FrontWidth.qOut k).isLt
  have hv := orT_val P tf k k0 h j
  rcases sh4_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> rw [e] at u <;> omega

/-- **Phase 1's run.** -/
theorem ph1_step (xs w : List Bool) (H : Fin (NW P tf) → ℕ) (A : Fin (NW P tf) → List Bool)
    (hP : PristineH P tf H A k0) (hx : A (xT P tf) = RepairOrdinary.frame xs) (hxH : H (xT P tf) = 0)
    (hw : A (wT P tf) = RepairOrdinary.frame w) (hwH : H (wT P tf) = 0)
    (hN : 2 ≤ xs.length) (hwl : 16 * w.length ≤ xs.length)
    (hℓ : natBitLength (Ledger.nativeWidth k Ap xs.length) ≤ xs.length + 1)
    (hq3 : 3 * natBitLength (Ledger.nativeWidth k Ap xs.length) ≤ Ledger.nativeWidth k Ap xs.length)
    (hsz1 : ∀ c : BooleanCircuit (Ledger.nativeWidth k Ap xs.length),
      CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap xs.length) (value (payload w.tail)) = some c →
        c.size + 1 ≤ 2 * xs.length + 2)
    (hsz2 : ∀ c : BooleanCircuit (Ledger.nativeWidth k Ap xs.length),
      CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap xs.length) (value (payload w.tail)) = some c →
        2 * natBitLength (Ledger.nativeWidth k Ap xs.length) + 2 * natBitLength c.size + 2 ≤ 2 * xs.length + 2) :
    ∃ (H' : Fin (NW P tf) → ℕ) (A' : Fin (NW P tf) → List Bool),
      Step (ph1M P tf k Ap G k0 h) ((8 * xs.length + 14) + 1 + (FrontWidthCost.qCost k Ap xs + 1 +
        (FrontOracle.osCost xs w (Ledger.nativeWidth k Ap xs.length) + 1 +
          FrontSizeStage.ssCost xs (2 ^ RecoveryScheduleEnvelope.oracleDepth G)))) H A H' A' ∧
      PristineH P tf H' A' (k0 + PH1 k) ∧
      (A' (qT P tf k k0 h) = List.replicate (Ledger.nativeWidth k Ap xs.length) true ∧ H' (qT P tf k k0 h) = 0) ∧
      (A' (orT P tf k k0 h 14) = [w.headD false] ∧ H' (orT P tf k k0 h 14) = 0) ∧
      (A' (orT P tf k k0 h 13) = RepairOrdinary.frame (restOf w.tail) ∧ H' (orT P tf k k0 h 13) = 0) ∧
      (A' (orT P tf k k0 h 11) = [FrontOracleField.okOf w] ∧ H' (orT P tf k k0 h 11) = 0) ∧
      (A' (orT P tf k k0 h FrontOracle.flagO) =
        [(CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap xs.length)
          (value (payload w.tail))).isSome] ∧ H' (orT P tf k k0 h FrontOracle.flagO) = 0) ∧
      ((∀ c : BooleanCircuit (Ledger.nativeWidth k Ap xs.length),
        CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap xs.length) (value (payload w.tail)) =
          some c → A' (orT P tf k k0 h FrontOracle.descO) = PCPPNative.descriptor c) ∧
        H' (orT P tf k k0 h FrontOracle.descO) = 0) ∧
      (A' (vT P tf k k0 h) = [FrontSizeStage.sizeVerdict G (Ledger.nativeWidth k Ap xs.length)
        (CanonicalWitnessCodec.decodeBooleanCircuit (Ledger.nativeWidth k Ap xs.length) (value (payload w.tail)))] ∧
        H' (vT P tf k k0 h) = 0) ∧
      (A' (xT P tf) = RepairOrdinary.frame xs ∧ H' (xT P tf) = 0) ∧
      (A' (wT P tf) = RepairOrdinary.frame w ∧ H' (wT P tf) = 0) ∧
      ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + k0 → A' y = A y ∧ H' y = H y := by
  set q := Ledger.nativeWidth k Ap xs.length with hqdef
  set o := CanonicalWitnessCodec.decodeBooleanCircuit q (value (payload w.tail)) with ho
  have hxL : (xT P tf).val < 2 := by rw [xT_val]; omega
  have hwL : (wT P tf).val < 2 := by rw [wT_val]; omega
  have hq := (FrontWidth.qOut k).isLt
  -- stage 1: the copy of `x`
  have i1 := sl1_inj P tf k k0 h
  have hlow1 : ∀ i a, sh1 P tf i = some a → a.val < 2 + NL P + k0 := fun i a hi => by
    unfold sh1 at hi; split_ifs at hi; cases hi; rw [xT_val]; omega
  have hL1 : ∀ i a, sh1 P tf i = some a → 2 + NL P ≤ a.val ∨ a.val < 2 := fun i a hi => by
    unfold sh1 at hi; split_ifs at hi; cases hi; right; exact hxL
  have r1 := dockAny (FrontLoopKit.step_of_rready (RecoveryColdWitnessCopy.copy_ready xs)) _ i1 H A
    (fun j => by
      by_cases hj : j.val = 0
      · rw [show j = 0 from Fin.ext hj, sl_some P tf _ k0 _ 0 _ (sh1_some0 P tf)]; exact hxH
      · rw [sl_none P tf _ k0 _ j (sh1_none P tf j hj)]; exact (pristineH_rg P tf k0 _ H A hP j).2)
    (fun j => by
      rw [copy_in]
      by_cases hj : j.val = 0
      · rw [if_pos hj, show j = 0 from Fin.ext hj, sl_some P tf _ k0 _ 0 _ (sh1_some0 P tf)]; exact hx
      · rw [if_neg hj, sl_none P tf _ k0 _ j (sh1_none P tf j hj)]; exact (pristineH_rg P tf k0 _ H A hP j).1)
  obtain ⟨H1, hH1⟩ : ∃ H1, H1 = dockH (sl P tf (sh1 P tf) k0 (h1 k k0 tf h)) H (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A1, hA1⟩ : ∃ A1, A1 = install (sl P tf (sh1 P tf) k0 (h1 k k0 tf h)) A
      (RecoveryColdWitnessCopy.output xs) := ⟨_, rfl⟩
  rw [← hH1, ← hA1] at r1
  have P1 : PristineH P tf H1 A1 (k0 + 4) := by
    rw [hH1, hA1]; exact pristineH_after P tf _ k0 _ hlow1 hL1 H A _ _ hP
  have a1x : A1 (xT P tf) = RepairOrdinary.frame xs := by
    rw [hA1, install_sh P tf _ k0 _ i1 A _ 0 _ (sh1_some0 P tf)]; rfl
  have h1x : H1 (xT P tf) = 0 := by rw [hH1, dockH_sh P tf _ k0 _ i1 H _ 0 _ (sh1_some0 P tf)]
  have a1c : A1 (cxT P tf k k0 h) = RepairOrdinary.frame xs := by
    rw [hA1, cxT, install_rg P tf _ k0 _ i1 A _ 1 (sh1_none P tf 1 (by decide))]; rfl
  have h1c : H1 (cxT P tf k k0 h) = 0 := by
    rw [hH1, cxT, dockH_rg P tf _ k0 _ i1 H _ 1 (sh1_none P tf 1 (by decide))]
  have low1 : ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + k0 → A1 y = A y ∧ H1 y = H y := by
    intro y hy1 hy2
    have hns : ∀ i a, sh1 P tf i = some a → a ≠ y := fun i a hi e => by
      unfold sh1 at hi; split_ifs at hi; cases hi; rw [← e, xT_val] at hy1; omega
    rw [hA1, hH1]
    exact ⟨install_low P tf _ k0 _ A _ y hy2 hns, dockH_low P tf _ k0 _ H _ y hy2 hns⟩
  have a1w : A1 (wT P tf) = A (wT P tf) ∧ H1 (wT P tf) = H (wT P tf) := by
    have hns : ∀ i a, sh1 P tf i = some a → a ≠ wT P tf := fun i a hi e => by
      unfold sh1 at hi; split_ifs at hi; cases hi; exact absurd (congrArg Fin.val e) (by simp [xT_val, wT_val])
    rw [hA1, hH1]
    exact ⟨install_low P tf _ k0 _ A _ _ (by rw [wT_val]; omega) hns,
      dockH_low P tf _ k0 _ H _ _ (by rw [wT_val]; omega) hns⟩
  -- stage 2: the width
  obtain ⟨out2, g2, o2q⟩ := FrontWidthCost.qMachine_ready_c k Ap xs
  have i2 := sl2_inj P tf k k0 h
  have hlow2 : ∀ i a, sh2 P tf k k0 h i = some a → a.val < 2 + NL P + (k0 + 4) := fun i a hi => by
    unfold sh2 at hi; split_ifs at hi; cases hi; simp only [cxT, rg_val, Fin.val_one]; omega
  have hL2 : ∀ i a, sh2 P tf k k0 h i = some a → 2 + NL P ≤ a.val ∨ a.val < 2 := fun i a hi => by
    unfold sh2 at hi; split_ifs at hi; cases hi; left; simp only [cxT, rg_val]; omega
  have r2 := dockAnyR g2 _ i2 H1 A1
    (fun j => by
      by_cases hj : j = FrontWidth.inT k
      · rw [sl_some P tf _ _ _ j (cxT P tf k k0 h) (by simp [sh2, hj])]; exact h1c
      · rw [sl_none P tf _ _ _ j (sh2_none P tf k k0 h j hj)]; exact (pristineH_rg P tf _ _ H1 A1 P1 j).2)
    (fun j => by
      by_cases hj : j = FrontWidth.inT k
      · rw [sl_some P tf _ _ _ j (cxT P tf k k0 h) (by simp [sh2, hj]), a1c]; simp [FrontWidth.qInput, hj]
      · rw [sl_none P tf _ _ _ j (sh2_none P tf k k0 h j hj), (pristineH_rg P tf _ _ H1 A1 P1 j).1]
        simp [FrontWidth.qInput, hj])
  obtain ⟨H2, hH2⟩ : ∃ H2, H2 = dockH (sl P tf (sh2 P tf k k0 h) (k0 + 4) (h2 k k0 tf h)) H1 (fun _ => 0) :=
    ⟨_, rfl⟩
  obtain ⟨A2, hA2⟩ : ∃ A2, A2 = install (sl P tf (sh2 P tf k k0 h) (k0 + 4) (h2 k k0 tf h)) A1 out2 := ⟨_, rfl⟩
  rw [← hH2, ← hA2] at r2
  have P2 : PristineH P tf H2 A2 (k0 + 4 + FrontWidth.QT k) := by
    rw [hH2, hA2]; exact pristineH_after P tf _ _ _ hlow2 hL2 H1 A1 _ _ P1
  have hns2 : ∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + 1) → ∀ i a, sh2 P tf k k0 h i = some a → a ≠ y :=
    fun y hy i a hi e => by
      unfold sh2 at hi; split_ifs at hi; cases hi; simp only [cxT] at e
      have := congrArg Fin.val e; rw [rg_val] at this; simp at this; omega
  have low2 : ∀ y : Fin (NW P tf), y.val < 2 + NL P + (k0 + 1) → A2 y = A1 y ∧ H2 y = H1 y := fun y hy => by
    rw [hA2, hH2]
    exact ⟨install_low P tf _ _ _ A1 _ y (by omega) (hns2 y hy), dockH_low P tf _ _ _ H1 _ y (by omega) (hns2 y hy)⟩
  have a2q : A2 (qT P tf k k0 h) = List.replicate q true := by
    rw [hA2, qT, install_rg P tf _ _ _ i2 A1 _ _ (sh2_none P tf k k0 h _ (qOut_ne_inT k))]; exact o2q
  have h2q : H2 (qT P tf k k0 h) = 0 := by
    rw [hH2, qT, dockH_rg P tf _ _ _ i2 H1 _ _ (sh2_none P tf k k0 h _ (qOut_ne_inT k))]
  -- stage 3: the oracle field
  obtain ⟨out3, g3, o14, o13, o11, oflag, odesc, o0, o1, o2⟩ := FrontOracle.oracle_ready xs w q hN hwl hℓ hq3
  have i3 := sl3_inj P tf k k0 h
  have hlow3 : ∀ i a, sh3 P tf k k0 h i = some a → a.val < 2 + NL P + (k0 + 4 + FrontWidth.QT k) :=
    fun i a hi => by rcases sh3_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega
  have hL3 : ∀ i a, sh3 P tf k k0 h i = some a → 2 + NL P ≤ a.val ∨ a.val < 2 :=
    fun i a hi => by rcases sh3_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega
  have e2x := low2 (xT P tf) (by rw [xT_val]; omega)
  have e2w := low2 (wT P tf) (by rw [wT_val]; omega)
  have r3 := dockAnyR g3 _ i3 H2 A2
    (fun j => by
      by_cases j0 : j.val = 0
      · rw [sl_some P tf _ _ _ j (xT P tf) (by simp [sh3, j0]), e2x.2, h1x]
      · by_cases j1 : j.val = 1
        · rw [sl_some P tf _ _ _ j (wT P tf) (by simp [sh3, j1]), e2w.2, a1w.2, hwH]
        · by_cases j2 : j.val = 2
          · rw [sl_some P tf _ _ _ j (qT P tf k k0 h) (by simp [sh3, j2]), h2q]
          · rw [sl_none P tf _ _ _ j (sh3_none P tf k k0 h j (by omega))]
            exact (pristineH_rg P tf _ _ H2 A2 P2 j).2)
    (fun j => by
      simp only [FrontOracle.osIn]
      by_cases j0 : j.val = 0
      · rw [if_pos j0, sl_some P tf _ _ _ j (xT P tf) (by simp [sh3, j0]), e2x.1, a1x]
      · by_cases j1 : j.val = 1
        · rw [if_neg j0, if_pos j1, sl_some P tf _ _ _ j (wT P tf) (by simp [sh3, j1]), e2w.1, a1w.1, hw]
        · by_cases j2 : j.val = 2
          · rw [if_neg j0, if_neg j1, if_pos j2, sl_some P tf _ _ _ j (qT P tf k k0 h) (by simp [sh3, j2]), a2q]
          · rw [if_neg j0, if_neg j1, if_neg j2, sl_none P tf _ _ _ j (sh3_none P tf k k0 h j (by omega))]
            exact (pristineH_rg P tf _ _ H2 A2 P2 j).1)
  obtain ⟨H3, hH3⟩ : ∃ H3, H3 = dockH (sl P tf (sh3 P tf k k0 h) (k0 + 4 + FrontWidth.QT k) (h3 k k0 tf h)) H2
      (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A3, hA3⟩ : ∃ A3, A3 = install (sl P tf (sh3 P tf k k0 h) (k0 + 4 + FrontWidth.QT k) (h3 k k0 tf h)) A2
      out3 := ⟨_, rfl⟩
  rw [← hH3, ← hA3] at r3
  have P3 : PristineH P tf H3 A3 (k0 + 4 + FrontWidth.QT k + FrontOracle.OS) := by
    rw [hH3, hA3]; exact pristineH_after P tf _ _ _ hlow3 hL3 H2 A2 _ _ P2
  have s3x : sh3 P tf k k0 h (0 : Fin FrontOracle.OS) = some (xT P tf) := rfl
  have s3w : sh3 P tf k k0 h (1 : Fin FrontOracle.OS) = some (wT P tf) := rfl
  have s3q : sh3 P tf k k0 h (2 : Fin FrontOracle.OS) = some (qT P tf k k0 h) := rfl
  have rd3 : ∀ j : Fin FrontOracle.OS, 3 ≤ j.val → A3 (orT P tf k k0 h j) = out3 j ∧ H3 (orT P tf k k0 h j) = 0 :=
    fun j hj => by
      rw [hA3, hH3, orT]
      exact ⟨install_rg P tf _ _ _ i3 A2 _ j (sh3_none P tf k k0 h j hj),
        dockH_rg P tf _ _ _ i3 H2 _ j (sh3_none P tf k k0 h j hj)⟩
  have a3x : A3 (xT P tf) = RepairOrdinary.frame xs ∧ H3 (xT P tf) = 0 := by
    rw [hA3, hH3, install_sh P tf _ _ _ i3 A2 _ 0 _ s3x, dockH_sh P tf _ _ _ i3 H2 _ 0 _ s3x]; exact ⟨o0, rfl⟩
  have a3w : A3 (wT P tf) = RepairOrdinary.frame w ∧ H3 (wT P tf) = 0 := by
    rw [hA3, hH3, install_sh P tf _ _ _ i3 A2 _ 1 _ s3w, dockH_sh P tf _ _ _ i3 H2 _ 1 _ s3w]; exact ⟨o1, rfl⟩
  have a3q : A3 (qT P tf k k0 h) = List.replicate q true ∧ H3 (qT P tf k k0 h) = 0 := by
    rw [hA3, hH3, install_sh P tf _ _ _ i3 A2 _ 2 _ s3q, dockH_sh P tf _ _ _ i3 H2 _ 2 _ s3q]; exact ⟨o2, rfl⟩
  have low3 : ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + (k0 + 4) → A3 y = A2 y ∧ H3 y = H2 y := by
    intro y hy1 hy2
    have hns : ∀ i a, sh3 P tf k k0 h i = some a → a ≠ y := fun i a hi e => by
      rcases sh3_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> rw [e] at u <;> omega
    rw [hA3, hH3]
    exact ⟨install_low P tf _ _ _ A2 _ y (by omega) hns, dockH_low P tf _ _ _ H2 _ y (by omega) hns⟩
  -- stage 4: the size check
  obtain ⟨out4, g4, v12, v0, v1, v2, v3⟩ := FrontSizeStage.size_ready xs q G o (out3 FrontOracle.descO)
    (fun c hc => (odesc c hc)) hsz1 hsz2
  have i4 := sl4_inj P tf k k0 h
  have hf3 := flag_val
  have hd3 := desc_val
  have hfO := FrontOracle.flagO.isLt
  have hdO := FrontOracle.descO.isLt
  have hlow4 : ∀ i a, sh4 P tf k k0 h i = some a →
      a.val < 2 + NL P + (k0 + 4 + FrontWidth.QT k + FrontOracle.OS) := fun i a hi => by
    rcases sh4_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega
  have hL4 : ∀ i a, sh4 P tf k k0 h i = some a → 2 + NL P ≤ a.val ∨ a.val < 2 := fun i a hi => by
    rcases sh4_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega
  have af := rd3 FrontOracle.flagO hf3.1
  have ad := rd3 FrontOracle.descO hd3.1
  have r4 := dockAnyR g4 _ i4 H3 A3
    (fun j => by
      by_cases j0 : j.val = 0
      · rw [sl_some P tf _ _ _ j (xT P tf) (by simp [sh4, j0])]; exact a3x.2
      · by_cases j1 : j.val = 1
        · rw [sl_some P tf _ _ _ j (orT P tf k k0 h FrontOracle.flagO) (by simp [sh4, j1])]; exact af.2
        · by_cases j2 : j.val = 2
          · rw [sl_some P tf _ _ _ j (orT P tf k k0 h FrontOracle.descO) (by simp [sh4, j2])]; exact ad.2
          · by_cases j3 : j.val = 3
            · rw [sl_some P tf _ _ _ j (qT P tf k k0 h) (by simp [sh4, j3])]; exact a3q.2
            · rw [sl_none P tf _ _ _ j (sh4_none P tf k k0 h j (by omega))]
              exact (pristineH_rg P tf _ _ H3 A3 P3 j).2)
    (fun j => by
      simp only [FrontSizeStage.ssIn]
      by_cases j0 : j.val = 0
      · rw [if_pos j0, sl_some P tf _ _ _ j (xT P tf) (by simp [sh4, j0])]; exact a3x.1
      · by_cases j1 : j.val = 1
        · rw [if_neg j0, if_pos j1, sl_some P tf _ _ _ j (orT P tf k k0 h FrontOracle.flagO) (by simp [sh4, j1]),
            af.1, oflag]
        · by_cases j2 : j.val = 2
          · rw [if_neg j0, if_neg j1, if_pos j2, sl_some P tf _ _ _ j (orT P tf k k0 h FrontOracle.descO)
              (by simp [sh4, j2]), ad.1]
          · by_cases j3 : j.val = 3
            · rw [if_neg j0, if_neg j1, if_neg j2, if_pos j3, sl_some P tf _ _ _ j (qT P tf k k0 h)
                (by simp [sh4, j3])]; exact a3q.1
            · rw [if_neg j0, if_neg j1, if_neg j2, if_neg j3, sl_none P tf _ _ _ j (sh4_none P tf k k0 h j (by omega))]
              exact (pristineH_rg P tf _ _ H3 A3 P3 j).1)
  obtain ⟨H4, hH4⟩ : ∃ H4, H4 = dockH (sl P tf (sh4 P tf k k0 h) (k0 + 4 + FrontWidth.QT k + FrontOracle.OS)
      (h4 k k0 tf h)) H3 (fun _ => 0) := ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A4, A4 = install (sl P tf (sh4 P tf k k0 h) (k0 + 4 + FrontWidth.QT k + FrontOracle.OS)
      (h4 k k0 tf h)) A3 out4 := ⟨_, rfl⟩
  rw [← hH4, ← hA4] at r4
  have P4 : PristineH P tf H4 A4 (k0 + 4 + FrontWidth.QT k + FrontOracle.OS + FrontSizeStage.ST) := by
    rw [hH4, hA4]; exact pristineH_after P tf _ _ _ hlow4 hL4 H3 A3 _ _ P3
  have s4x : sh4 P tf k k0 h (0 : Fin FrontSizeStage.ST) = some (xT P tf) := rfl
  have s4f : sh4 P tf k k0 h (1 : Fin FrontSizeStage.ST) = some (orT P tf k k0 h FrontOracle.flagO) := rfl
  have s4d : sh4 P tf k k0 h (2 : Fin FrontSizeStage.ST) = some (orT P tf k k0 h FrontOracle.descO) := rfl
  have s4q : sh4 P tf k k0 h (3 : Fin FrontSizeStage.ST) = some (qT P tf k k0 h) := rfl
  have rd4O : ∀ j : Fin FrontOracle.OS, 3 ≤ j.val → j.val ≠ FrontOracle.flagO.val → j.val ≠ FrontOracle.descO.val →
      A4 (orT P tf k k0 h j) = out3 j ∧ H4 (orT P tf k k0 h j) = 0 := fun j hj hjf hjd => by
    have hv := orT_val P tf k k0 h j
    have hjl := j.isLt
    rw [hA4, hH4, install_low P tf _ _ _ A3 _ _ (by omega) (sh4_ne_orT P tf k k0 h j hjf hjd),
      dockH_low P tf _ _ _ H3 _ _ (by omega) (sh4_ne_orT P tf k k0 h j hjf hjd)]
    exact rd3 j hj
  have low4 : ∀ y : Fin (NW P tf), 2 ≤ y.val → y.val < 2 + NL P + (k0 + 4) → A4 y = A3 y ∧ H4 y = H3 y := by
    intro y hy1 hy2
    have hns : ∀ i a, sh4 P tf k k0 h i = some a → a ≠ y := fun i a hi e => by
      rcases sh4_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> rw [e] at u <;> omega
    rw [hA4, hH4]
    exact ⟨install_low P tf _ _ _ A3 _ y (by omega) hns, dockH_low P tf _ _ _ H3 _ y (by omega) hns⟩
  have hwne : ∀ i a, sh4 P tf k k0 h i = some a → a ≠ wT P tf := fun i a hi e => by
    have := congrArg Fin.val e
    rw [wT_val] at this
    rcases sh4_some P tf k k0 h i a hi with ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ | ⟨_, u⟩ <;> omega
  have k4 : k0 + 4 + FrontWidth.QT k + FrontOracle.OS + FrontSizeStage.ST = k0 + PH1 k := by unfold PH1; omega
  refine ⟨H4, A4, Step.seq r1 (Step.seq r2 (Step.seq r3 r4)), k4 ▸ P4, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hA4, hH4, install_sh P tf _ _ _ i4 A3 _ 3 _ s4q, dockH_sh P tf _ _ _ i4 H3 _ 3 _ s4q]; exact ⟨v3, rfl⟩
  · have e := rd4O 14 (by decide) (by decide) (by decide)
    rw [e.1, o14]; exact ⟨rfl, e.2⟩
  · have e := rd4O 13 (by decide) (by decide) (by decide)
    rw [e.1, o13]; exact ⟨rfl, e.2⟩
  · have e := rd4O 11 (by decide) (by decide) (by decide)
    rw [e.1, o11]; exact ⟨rfl, e.2⟩
  · rw [hA4, hH4, install_sh P tf _ _ _ i4 A3 _ 1 _ s4f, dockH_sh P tf _ _ _ i4 H3 _ 1 _ s4f]; exact ⟨v1, rfl⟩
  · refine ⟨fun c hc => ?_, ?_⟩
    · rw [hA4, install_sh P tf _ _ _ i4 A3 _ 2 _ s4d, v2]; exact odesc c hc
    · rw [hH4, dockH_sh P tf _ _ _ i4 H3 _ 2 _ s4d]
  · rw [hA4, hH4, vT, install_rg P tf _ _ _ i4 A3 _ _ (sh4_none P tf k k0 h _ (by decide)),
      dockH_rg P tf _ _ _ i4 H3 _ _ (sh4_none P tf k k0 h _ (by decide))]
    exact ⟨v12, rfl⟩
  · rw [hA4, hH4, install_sh P tf _ _ _ i4 A3 _ 0 _ s4x, dockH_sh P tf _ _ _ i4 H3 _ 0 _ s4x]; exact ⟨v0, rfl⟩
  · rw [hA4, hH4, install_low P tf _ _ _ A3 _ _ (by rw [wT_val]; omega) hwne,
      dockH_low P tf _ _ _ H3 _ _ (by rw [wT_val]; omega) hwne]
    exact a3w
  · intro y hy1 hy2
    have e4 := low4 y hy1 (by omega)
    have e3 := low3 y hy1 (by omega)
    have e2 := low2 y (by omega)
    have e1 := low1 y hy1 hy2
    exact ⟨by rw [e4.1, e3.1, e2.1, e1.1], by rw [e4.2, e3.2, e2.2, e1.2]⟩

end Ph

end NearCubicWires.WireExponent3_5.UnionMachine.FrontPh1
