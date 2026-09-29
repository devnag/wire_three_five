import Proof.Wire_3_5.FinalPass.Core6

/-! # S5Core, part 7: the core's room on the bank, the count and the mode stages (P3:3083-3086, 3170-3181)

On a bank `L : S5Lay nw` with the core's room `hR.coreE : Fin mC ↪ Fin L.t` (`HalfRoom2`), the core's programs run on
consecutive blocks of the room (`blk o sz`): the count on `[0, 5)`, the mode on `[5, 10)`, then the writers. Here:

* `blk`, `blk_inj`, `blk_ne` (disjoint blocks), `blk_ne0`, `blk_ne_wd`, `blk_ne_tN`, `blk_ne_tD`, `blk_reg`;
* `cellP`, `cell_exec`; the count's slots `cntSlots`, machine `cntM`, **`cnt_stage`** (from the framed input: the
  template `sent N`, the reference `sent (K·N^D)`, the block within `K·N^D + 1`, every other tape kept);
* the mode's slots `modeSlots`, machine `modeM`, **`mode_stage`** (the mode bit `[mb]` on its tape, the template kept,
  the block within `N + 1`, every other tape kept).

Paper quantities: the front's exact register length (`FrontOut.blank`) and the request's mode bit (P3:3083-3086). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

namespace NearCubicWires.WireExponent3_5.FinalPass.Core
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.WireExponent3_5.FinalPass.Tm NearCubicWires.WireExponent3_5.PrimAsm.S5Seam
open NearCubicWires.WireExponent3_5.FinalPass.S5T (sent sent_length read_sent)
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other install_existing)
open NearCubicWires.WireExponent3_5.PrimAsm.DockW (tape_cases sTape_inj rTape_inj sTape_ne_c sTape_ne_r cTape_ne_r
  wenc_A_c wenc_H_c sTape_val rTape_val cTape_val)

section Lay
variable {nw : ℕ} (L : S5Lay nw) {mTh mC : ℕ} (hR : Bank.HalfRoom2 L mTh mC)

/-- The input tape. -/
def i0 : Fin L.t := ⟨0, L.ht⟩

/-- **A block of the core's room**: tapes `o, …, o + sz − 1`. -/
def blk (o sz : ℕ) (h : o + sz ≤ mC) (j : Fin sz) : Fin L.t := hR.coreE ⟨o + j.val, by omega⟩

theorem blk_inj (o sz : ℕ) (h : o + sz ≤ mC) : Function.Injective (blk L hR o sz h) := by
  intro a b e
  have := congrArg Fin.val (hR.coreE.injective e)
  simp only at this
  exact Fin.ext (by omega)

theorem blk_ne (o1 sz1 : ℕ) (h1 : o1 + sz1 ≤ mC) (o2 sz2 : ℕ) (h2 : o2 + sz2 ≤ mC) (hd : o1 + sz1 ≤ o2)
    (j1 : Fin sz1) (j2 : Fin sz2) : blk L hR o1 sz1 h1 j1 ≠ blk L hR o2 sz2 h2 j2 := by
  intro e
  have := congrArg Fin.val (hR.coreE.injective e)
  simp only at this
  have := j1.isLt
  omega

theorem core_off (i : Fin mC) :
    (hR.coreE i).val ≠ 0 ∧ (∀ k, hR.coreE i ≠ L.wd k) ∧ hR.coreE i ≠ L.tN ∧ hR.coreE i ≠ L.tD :=
  L.coreOff _ (hR.coreE_sc i)

theorem blk_ne0 (o sz : ℕ) (h : o + sz ≤ mC) (j : Fin sz) : blk L hR o sz h j ≠ i0 L := fun e =>
  (core_off L hR _).1 (by rw [show (hR.coreE _) = i0 L from e]; rfl)

end Lay

/-! ## One action: a cell written -/

section Cell
variable {t : ℕ}

/-- Write `false` on a blank tape. -/
def cellP (cl : Fin t) : Prog t := .act (writeAt cl false) (fun _ => .stay)

theorem cell_exec (cl : Fin t) (A : Fin t → List Bool) (h : A cl = []) :
    Step (cellP cl).compile 1 (fun _ => 0) A (fun _ => 0) (Function.update A cl [false]) := by
  refine (Exec.step (Exec.act ⟨fun _ => 0, A⟩ (writeAt cl false) (fun _ => HeadMove.stay))).congr rfl (funext fun i => ?_)
  by_cases hi : i = cl
  · subst hi; simp [Bank.act, writeAt, h, writeTapeBit]
  · simp [Bank.act, writeAt, hi, Function.update_of_ne hi]

end Cell

/-! ## The count's stage -/

section Count
variable {nw : ℕ} (L : S5Lay nw) {mTh mC : ℕ} (hR : Bank.HalfRoom2 L mTh mC) (h5 : 0 + (3 + 2 + 0) ≤ mC)

/-- The count's slots: its input on the bank's input tape, the rest on the room's block `[0, 5)`. -/
noncomputable def cntSlots : Fin (3 + 2 + 0) → Fin L.t :=
  wslots (ns := 3) (nr := 0) cI (fun k : Fin 0 => k.elim0) (i0 L) (fun k : Fin 0 => k.elim0) (blk L hR 0 (3 + 2 + 0) h5)

theorem cntSlots_inj : Function.Injective (cntSlots L hR h5) :=
  wslots_inj _ _ _ _ _ (fun a _ _ => a.elim0) (fun k => k.elim0) (fun a _ _ => a.elim0) (blk_inj L hR 0 (3 + 2 + 0) h5)
    (fun k => k.elim0) (blk_ne0 L hR 0 (3 + 2 + 0) h5) (fun k => k.elim0)

/-- **The count's machine**: its cell written, then `cntW K D` focused. -/
noncomputable def cntM (K D : ℕ) :=
  Composition.machine (cellP (blk L hR 0 (3 + 2 + 0) h5 (cTape (ns := 3) (nr := 0)))).compile
    (RecoveryFocus.machine (cntSlots L hR h5) (cntW K D).toProg.compile)

theorem cntSlots_room (j : Fin (3 + 2 + 0)) (hj : j ≠ sTape (nr := 0) cI) : cntSlots L hR h5 j = blk L hR 0 (3 + 2 + 0) h5 j :=
  wslots_room _ _ _ _ _ j hj (fun k => k.elim0)

/-- The count's entry state. -/
def cntIn (u : List Bool) : WState 3 0 := ⟨fun _ => 0, fun i => if i = cI then frame u else [], fun q => q.elim0, false⟩

theorem cntIn_I (u : List Bool) : (cntIn u).st cI = frame u := by simp [cntIn]

theorem cntIn_o (u : List Bool) (i : Fin 4) (hi : i ≠ cI) : (cntIn u).st i = [] := by
  simp only [cntIn]; rw [if_neg hi]

theorem cntSlots_in : cntSlots L hR h5 (sTape (nr := 0) cI) = i0 L := wslots_in _ _ _ _ _

theorem cntSlots_ne (y : Fin L.t) (hy0 : y ≠ i0 L) (hy : ∀ j, y ≠ blk L hR 0 (3 + 2 + 0) h5 j) :
    ∀ j, cntSlots L hR h5 j ≠ y :=
  wslots_ne (ns := 3) (nr := 0) cI _ (i0 L) _ (blk L hR 0 (3 + 2 + 0) h5) y hy0 (fun k => k.elim0)
    (fun j _ _ => hy j) (fun a _ _ => a.elim0) (fun k => k.elim0)

/-- The room tape under the count's input slot is no slot. -/
theorem cntSlots_ne_in : ∀ j, cntSlots L hR h5 j ≠ blk L hR 0 (3 + 2 + 0) h5 (sTape (nr := 0) cI) :=
  wslots_ne (ns := 3) (nr := 0) cI _ (i0 L) _ (blk L hR 0 (3 + 2 + 0) h5) _ (blk_ne0 L hR 0 (3 + 2 + 0) h5 _)
    (fun k => k.elim0) (fun _ a _ e => a ((blk_inj L hR 0 (3 + 2 + 0) h5) e).symm) (fun a _ _ => a.elim0)
    (fun k => k.elim0)

/-- **The count's stage.** -/
theorem cnt_stage (K D : ℕ) (u : List Bool) (A : Fin L.t → List Bool) (hA0 : A (i0 L) = frame u)
    (hAb : ∀ j, A (blk L hR 0 (3 + 2 + 0) h5 j) = []) :
    ∃ A1 : Fin L.t → List Bool, Step (cntM L hR h5 K D) (1 + 1 + cntCost u.length K D) (fun _ => 0) A (fun _ => 0) A1 ∧
      A1 (i0 L) = frame u ∧ A1 (blk L hR 0 (3 + 2 + 0) h5 (sTape (nr := 0) cT)) = sent (u.length + 1) ∧
      A1 (blk L hR 0 (3 + 2 + 0) h5 (sTape (nr := 0) (cOut D))) = sent (K * (u.length + 1) ^ D) ∧
      (∀ j, (A1 (blk L hR 0 (3 + 2 + 0) h5 j)).length ≤ max (u.length + 2) (K * (u.length + 1) ^ D + 1)) ∧
      (∀ y, (∀ j, y ≠ blk L hR 0 (3 + 2 + 0) h5 j) → A1 y = A y) := by
  classical
  have hc := cell_exec (blk L hR 0 (3 + 2 + 0) h5 (cTape (ns := 3) (nr := 0))) A (hAb _)
  set A' := Function.update A (blk L hR 0 (3 + 2 + 0) h5 (cTape (ns := 3) (nr := 0))) [false] with hA'
  have hx := cntW_spec 0 K D u (cntIn u) (cntIn_I u) (fun _ => rfl) (cntIn_o u cT (by decide))
    (cntIn_o u cX (by decide)) (cntIn_o u cY (by decide))
  set τ := zSt ((cntIn u).sets cT (sent (u.length + 1))) (u.length + 1) K D with hτ
  have hi := cntSlots_inj L hR h5
  have h0c : i0 L ≠ blk L hR 0 (3 + 2 + 0) h5 (cTape (ns := 3) (nr := 0)) := fun e =>
    blk_ne0 L hR 0 (3 + 2 + 0) h5 _ e.symm
  have hA : ∀ j, A' (cntSlots L hR h5 j) = ZeroPadding.pad (Bridge.pc 3 0 0 j) ((wenc 0 (cntIn u)).A j) := by
    refine entry_eq _ 0 0 le_rfl (cntIn u) (fun q => q.elim0) A' (fun i => ?_) ?_ (fun q => q.elim0)
    · by_cases hi0 : i = cI
      · subst hi0
        rw [cntSlots_in, hA', Function.update_of_ne h0c, hA0, cntIn_I]
      · rw [cntSlots_room L hR h5 _ (fun e => hi0 (sTape_inj e)), hA',
          Function.update_of_ne (fun e => sTape_ne_c i ((blk_inj L hR 0 (3 + 2 + 0) h5) e)), hAb, cntIn_o u i hi0]
    · rw [cntSlots_room L hR h5 _ (fun e => sTape_ne_c (nr := 0) cI e.symm), hA', Function.update_self]
      rfl
  have hτs : ∀ i, τ.sh i = 0 := fun i => rfl
  have hd := dock_step (cntW K D) _ hi 0 0 (cntIn u) τ _ hx (fun _ => rfl) (fun q => q.elim0) hτs (fun q => q.elim0)
    A' hA
  have hI : τ.st cI = frame u := by
    rw [hτ, zSt_o _ _ _ _ cI (by decide) (by decide)]
    simp only [WState.sets_st]; rw [Function.update_of_ne (by decide), cntIn_I]
  refine ⟨_, Step.seq hc hd, ?_, ?_, ?_, ?_, ?_⟩
  · have h := exit_s (cntSlots L hR h5) hi 0 0 τ A' cI
    rw [cntSlots_in] at h
    rw [h, hI]
  · have h := exit_s (cntSlots L hR h5) hi 0 0 τ A' cT
    rw [cntSlots_room L hR h5 _ (fun e => absurd (sTape_inj e) (by decide))] at h
    rw [h, hτ, zSt_o _ _ _ _ cT cTX cTY]
    simp only [WState.sets_st]; rw [Function.update_self]
  · have h := exit_s (cntSlots L hR h5) hi 0 0 τ A' (cOut D)
    rw [cntSlots_room L hR h5 _ (fun e => by
      have := sTape_inj e; unfold cOut at this; split_ifs at this <;> exact absurd this (by decide))] at h
    rw [h, hτ, zSt_out]
  · intro j
    have hN : 1 ≤ u.length + 1 := by omega
    rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, _⟩
    · by_cases hi0 : i = cI
      · subst hi0
        rw [install_other (cntSlots L hR h5) A' _ _ (cntSlots_ne_in L hR h5), hA',
          Function.update_of_ne (fun e => sTape_ne_c (nr := 0) cI ((blk_inj L hR 0 (3 + 2 + 0) h5) e)), hAb]
        simp
      · rw [← cntSlots_room L hR h5 _ (fun e => hi0 (sTape_inj e)), exit_s _ hi, hτ]
        have hX := zX_len_le (u.length + 1) K D hN
        have hY := zY_len_le (u.length + 1) K D hN
        by_cases hX' : i = cX
        · subst hX'; rw [zSt_X]; exact le_max_of_le_right hX
        · by_cases hY' : i = cY
          · subst hY'; rw [zSt_Y]; exact le_max_of_le_right hY
          · have hT' : i = cT := by
              revert hi0 hX' hY'; revert i; decide
            subst hT'
            rw [zSt_o _ _ _ _ cT cTX cTY]
            simp only [WState.sets_st]; rw [Function.update_self, sent_length]; exact le_max_left _ _
    · rw [← cntSlots_room L hR h5 _ (fun e => sTape_ne_c (nr := 0) cI e.symm), exit_c _ hi]; simp
    · exact q.elim0
  · intro y hy
    by_cases hy0 : y = i0 L
    · subst hy0
      have h := exit_s (cntSlots L hR h5) hi 0 0 τ A' cI
      rw [cntSlots_in] at h
      rw [h, hI, hA0]
    · rw [install_other (cntSlots L hR h5) A' _ _ (cntSlots_ne L hR h5 y hy0 hy), hA', Function.update_of_ne (hy _)]

end Count

/-! ## The mode's stage -/

section Mode
variable {nw : ℕ} (L : S5Lay nw) {mTh mC : ℕ} (hR : Bank.HalfRoom2 L mTh mC) (h10 : 5 + (3 + 2 + 0) ≤ mC)
  (cTt : Fin L.t)

/-- The mode program's slots: its input on the bank's input tape, its template on the count's template `cTt`, the
rest on the room's block `[5, 10)`. -/
noncomputable def modeSlots : Fin (3 + 2 + 0) → Fin L.t :=
  wslots (ns := 3) (nr := 0) mI (![mT] : Fin 1 → Fin 4) (i0 L) (![cTt] : Fin 1 → Fin L.t) (blk L hR 5 (3 + 2 + 0) h10)

theorem modeSlots_inj (h0 : cTt ≠ i0 L) (hb : ∀ j, cTt ≠ blk L hR 5 (3 + 2 + 0) h10 j) :
    Function.Injective (modeSlots L hR h10 cTt) :=
  wslots_inj _ _ _ _ _ (fun a b _ => Subsingleton.elim a b) (fun k => by fin_cases k; decide)
    (fun a b _ => Subsingleton.elim a b) (blk_inj L hR 5 (3 + 2 + 0) h10) (fun k => by fin_cases k; exact h0)
    (blk_ne0 L hR 5 (3 + 2 + 0) h10) (fun k j => by fin_cases k; exact hb j)

/-- **The mode's machine**: its cell written, then `modeW` focused. -/
noncomputable def modeM :=
  Composition.machine (cellP (blk L hR 5 (3 + 2 + 0) h10 (cTape (ns := 3) (nr := 0)))).compile
    (RecoveryFocus.machine (modeSlots L hR h10 cTt) modeW.toProg.compile)

/-- The mode program's entry state. -/
def modeIn (u : List Bool) (N : ℕ) : WState 3 0 :=
  ⟨fun _ => 0, fun i => if i = mI then frame u else if i = mT then sent N else [], fun q => q.elim0, false⟩

theorem modeSlots_in : modeSlots L hR h10 cTt (sTape (nr := 0) mI) = i0 L := wslots_in _ _ _ _ _

theorem modeSlots_T : modeSlots L hR h10 cTt (sTape (nr := 0) mT) = cTt :=
  wslots_out (ns := 3) (nr := 0) mI (![mT] : Fin 1 → Fin 4) (i0 L) (![cTt] : Fin 1 → Fin L.t) _
    (fun a b _ => Subsingleton.elim a b) (fun k => by fin_cases k; decide) 0

theorem modeSlots_room (j : Fin (3 + 2 + 0)) (h1 : j ≠ sTape (nr := 0) mI) (h2 : j ≠ sTape (nr := 0) mT) :
    modeSlots L hR h10 cTt j = blk L hR 5 (3 + 2 + 0) h10 j :=
  wslots_room _ _ _ _ _ j h1 (fun k => by fin_cases k; exact fun e => h2 e.symm)

theorem modeSlots_ne (y : Fin L.t) (hy0 : y ≠ i0 L) (hyT : y ≠ cTt) (hy : ∀ j, j ≠ sTape (nr := 0) mI →
    j ≠ sTape (nr := 0) mT → y ≠ blk L hR 5 (3 + 2 + 0) h10 j) : ∀ j, modeSlots L hR h10 cTt j ≠ y :=
  wslots_ne (ns := 3) (nr := 0) mI _ (i0 L) _ (blk L hR 5 (3 + 2 + 0) h10) y hy0 (fun k => by fin_cases k; exact hyT)
    (fun j a b => hy j a (fun e => b 0 e.symm)) (fun a b _ => Subsingleton.elim a b) (fun k => by fin_cases k; decide)

/-- **The mode's stage**: from the framed request word `1^L 0 bits mb rest` and the count's template `sent N`
(`4L + 3 ≤ 2N`), the bit `[mb]` on the mode tape. -/
theorem mode_stage (h0 : cTt ≠ i0 L) (hb : ∀ j, cTt ≠ blk L hR 5 (3 + 2 + 0) h10 j) (Ln N : ℕ) (bits : List Bool)
    (mb : Bool) (rest : List Bool) (hbl : bits.length = Ln) (hN : 4 * Ln + 3 ≤ 2 * N) (A : Fin L.t → List Bool)
    (hA0 : A (i0 L) = frame (List.replicate Ln true ++ false :: (bits ++ mb :: rest))) (hAT : A cTt = sent N)
    (hAb : ∀ j, A (blk L hR 5 (3 + 2 + 0) h10 j) = []) :
    ∃ A2 : Fin L.t → List Bool, Step (modeM L hR h10 cTt) (1 + 1 + modeCost Ln N) (fun _ => 0) A (fun _ => 0) A2 ∧
      A2 (blk L hR 5 (3 + 2 + 0) h10 (sTape (nr := 0) mM)) = [mb] ∧
      (∀ j, (A2 (blk L hR 5 (3 + 2 + 0) h10 j)).length ≤ Ln + 1) ∧
      (∀ y, (∀ j, y ≠ blk L hR 5 (3 + 2 + 0) h10 j) → A2 y = A y) := by
  classical
  set w := List.replicate Ln true ++ false :: (bits ++ mb :: rest) with hw
  have hc := cell_exec (blk L hR 5 (3 + 2 + 0) h10 (cTape (ns := 3) (nr := 0))) A (hAb _)
  set A' := Function.update A (blk L hR 5 (3 + 2 + 0) h10 (cTape (ns := 3) (nr := 0))) [false] with hA'
  have hσI : (modeIn w N).st mI = frame w := by simp [modeIn]
  have hσT : (modeIn w N).st mT = sent N := by simp only [modeIn]; rw [if_neg mIT.symm]; simp
  have hσQ : (modeIn w N).st mQ = [] := by simp only [modeIn]; rw [if_neg mIQ.symm, if_neg mTQ.symm]
  have hσM : (modeIn w N).st mM = [] := by simp only [modeIn]; rw [if_neg mIM.symm, if_neg mTM.symm]
  have hx := modeW_spec 0 Ln N bits mb rest hbl hN (modeIn w N) hσI hσT hσQ hσM (fun _ => rfl)
  set τ := ((modeIn w N).sets mQ (sent Ln)).sets mM [mb] with hτ
  have hi := modeSlots_inj L hR h10 cTt h0 hb
  have hcne : ∀ i : Fin 4, blk L hR 5 (3 + 2 + 0) h10 (sTape (nr := 0) i) ≠
      blk L hR 5 (3 + 2 + 0) h10 (cTape (ns := 3) (nr := 0)) := fun i e =>
    sTape_ne_c i ((blk_inj L hR 5 (3 + 2 + 0) h10) e)
  have hA : ∀ j, A' (modeSlots L hR h10 cTt j) = ZeroPadding.pad (Bridge.pc 3 0 0 j) ((wenc 0 (modeIn w N)).A j) := by
    refine entry_eq _ 0 0 le_rfl (modeIn w N) (fun q => q.elim0) A' (fun i => ?_) ?_ (fun q => q.elim0)
    · by_cases hiI : i = mI
      · subst hiI
        rw [modeSlots_in, hA', Function.update_of_ne (fun e => blk_ne0 L hR 5 (3 + 2 + 0) h10 _ e.symm), hA0, hσI]
      · by_cases hiT : i = mT
        · subst hiT
          rw [modeSlots_T, hA', Function.update_of_ne (fun e => hb _ e), hAT, hσT]
        · rw [modeSlots_room L hR h10 cTt _ (fun e => hiI (sTape_inj e)) (fun e => hiT (sTape_inj e)), hA',
            Function.update_of_ne (hcne i), hAb]
          simp only [modeIn]; rw [if_neg hiI, if_neg hiT]
    · rw [modeSlots_room L hR h10 cTt _ (fun e => sTape_ne_c (nr := 0) mI e.symm)
        (fun e => sTape_ne_c (nr := 0) mT e.symm), hA', Function.update_self]
      rfl
  have hd := dock_step modeW _ hi 0 0 (modeIn w N) τ _ hx (fun _ => rfl) (fun q => q.elim0) (fun _ => rfl)
    (fun q => q.elim0) A' hA
  have hτI : τ.st mI = frame w := by
    rw [hτ]; simp only [WState.sets_st]; rw [Function.update_of_ne mIM, Function.update_of_ne mIQ, hσI]
  have hτT : τ.st mT = sent N := by
    rw [hτ]; simp only [WState.sets_st]; rw [Function.update_of_ne mTM, Function.update_of_ne mTQ, hσT]
  have hτQ : τ.st mQ = sent Ln := by
    rw [hτ]; simp only [WState.sets_st]; rw [Function.update_of_ne mQM, Function.update_self]
  have hτM : τ.st mM = [mb] := by rw [hτ]; simp only [WState.sets_st]; rw [Function.update_self]
  refine ⟨_, Step.seq hc hd, ?_, ?_, ?_⟩
  · have h := exit_s (modeSlots L hR h10 cTt) hi 0 0 τ A' mM
    rw [modeSlots_room L hR h10 cTt _ (fun e => absurd (sTape_inj e) (by decide))
      (fun e => absurd (sTape_inj e) (by decide))] at h
    rw [h, hτM]
  · intro j
    rcases tape_cases j with ⟨i, rfl⟩ | rfl | ⟨q, _⟩
    · by_cases hiI : i = mI
      · subst hiI
        rw [install_other (modeSlots L hR h10 cTt) A' _ _ (modeSlots_ne L hR h10 cTt _
          (blk_ne0 L hR 5 (3 + 2 + 0) h10 _) (fun e => hb _ e.symm)
          (fun j a _ e => a ((blk_inj L hR 5 (3 + 2 + 0) h10) e).symm)), hA', Function.update_of_ne (hcne _), hAb]
        simp
      · by_cases hiT : i = mT
        · subst hiT
          rw [install_other (modeSlots L hR h10 cTt) A' _ _ (modeSlots_ne L hR h10 cTt _
            (blk_ne0 L hR 5 (3 + 2 + 0) h10 _) (fun e => hb _ e.symm)
            (fun j _ b e => b ((blk_inj L hR 5 (3 + 2 + 0) h10) e).symm)), hA', Function.update_of_ne (hcne _), hAb]
          simp
        · rw [← modeSlots_room L hR h10 cTt _ (fun e => hiI (sTape_inj e)) (fun e => hiT (sTape_inj e)), exit_s _ hi]
          by_cases hiQ : i = mQ
          · subst hiQ; rw [hτQ, sent_length]
          · have hiM : i = mM := by revert hiI hiT hiQ; revert i; decide
            subst hiM; rw [hτM]; simp
    · rw [← modeSlots_room L hR h10 cTt _ (fun e => sTape_ne_c (nr := 0) mI e.symm)
        (fun e => sTape_ne_c (nr := 0) mT e.symm), exit_c _ hi]; simp
    · exact q.elim0
  · intro y hy
    by_cases hy0 : y = i0 L
    · subst hy0
      have h := exit_s (modeSlots L hR h10 cTt) hi 0 0 τ A' mI
      rw [modeSlots_in] at h
      rw [h, hτI, hA0]
    · by_cases hyT : y = cTt
      · rw [hyT]
        have h := exit_s (modeSlots L hR h10 cTt) hi 0 0 τ A' mT
        rw [modeSlots_T] at h
        rw [h, hτT, hAT]
      · rw [install_other (modeSlots L hR h10 cTt) A' _ _ (modeSlots_ne L hR h10 cTt y hy0 hyT (fun j _ _ => hy j)),
          hA', Function.update_of_ne (hy _)]

end Mode

end NearCubicWires.WireExponent3_5.FinalPass.Core
