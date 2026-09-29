import Proof.Wire_3_5.UnionMachine.FrontWM

/-! # C6 front, the chain's kit: any word program docked on the worker's tapes

Every word-program stage of the front's chain (the source formats, the numbers, the counts) runs the same way: its
registers filled from the count `1^W` and its cell written (`FrontWM.wfM`), the program compiled and rewound, on the
worker's tapes, with the streams it reads SHARED with earlier stages' outputs and everything else on a fresh region.
* `streamOf`, `shW ins cntT` (the shared tapes: the streams `ins` names, the count), **`wfD`** (the docked stage),
  `stT` (the front tape of a stream);
* **`wfD_step`**: from a word program's run between clear states, the stage's run on the worker's tapes: every stream's
  front tape ends with the exit state's stream, the count is kept, nothing else outside the stage's tapes changes,
  the front's tapes past the region are still blank, all heads at `0`.

Paper quantity: none (the front's plumbing). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontWfDock
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.Cost NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine NearCubicWires.WireExponent3_5.UnionMachine.Plan
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

section Dock
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)
  {ns nr : ℕ}

/-- The stream a local tape carries (tape `0` and tapes `2 … ns+1`). -/
def streamOf (j : Fin (WT ns nr)) : Option (Fin (ns + 1)) :=
  if j.val = 0 then some 0 else if h : 2 ≤ j.val ∧ j.val ≤ ns + 1 then some ⟨j.val - 1, by omega⟩ else none

theorem streamOf_sTape (i : Fin (ns + 1)) : streamOf (encL (ns := ns) (nr := nr) (sTape i)) = some i := by
  have hv : (encL (ns := ns) (nr := nr) (sTape i)).val = if i.val = 0 then 0 else i.val + 1 := rfl
  have hi := i.isLt
  unfold streamOf
  split_ifs with h1 h2
  · rw [hv] at h1
    by_cases h0 : i.val = 0
    · exact congrArg some (Fin.ext (by simp [h0]))
    · rw [if_neg h0] at h1; omega
  · congr 1
    apply Fin.ext
    simp only
    rw [hv]
    rw [hv] at h1
    split_ifs at h1 ⊢ with h0
    · omega
    · omega
  · exfalso
    rw [hv] at h1 h2
    split_ifs at h1 h2 with h0 <;> omega

theorem streamOf_some (j : Fin (WT ns nr)) (i : Fin (ns + 1)) (h : streamOf j = some i) :
    j = encL (sTape (nr := nr) i) := by
  unfold streamOf at h
  apply Fin.ext
  rw [encL_val]
  have hv : (sTape (ns := ns) (nr := nr) i).val = if i.val = 0 then 0 else i.val + 1 := rfl
  split_ifs at h with h1 h2
  · have e := (Option.some.inj h).symm; subst e; rw [hv]; simp [h1]
  · have e := (Option.some.inj h).symm; subst e; rw [hv]; simp only; rw [if_neg (by omega)]; omega

/-- The dock's shared tapes: the streams `ins` names, and the count. -/
noncomputable def shW (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (j : Fin (WT ns nr)) :
    Option (Fin (NW P tf)) :=
  if j.val = ns + 2 + nr + 2 then some cntT else (streamOf j).bind ins

/-- **A word program docked**: its fill, its cell, the program rewound, at the shared tapes and a region at `k0`. -/
noncomputable def wfD (Pm : WM ns nr) (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (k0 : ℕ)
    (hk : k0 + WT ns nr ≤ tf) :=
  RecoveryFocus.machine (sl P tf (shW P tf ins cntT) k0 hk) (wfM Pm)

/-- The front tape of stream `i`. -/
noncomputable def stT (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (k0 : ℕ)
    (hk : k0 + WT ns nr ≤ tf) (i : Fin (ns + 1)) : Fin (NW P tf) :=
  sl P tf (shW P tf ins cntT) k0 hk (encL (sTape (nr := nr) i))

theorem stT_some (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (k0 : ℕ)
    (hk : k0 + WT ns nr ≤ tf) (i : Fin (ns + 1)) (a : Fin (NW P tf)) (h : ins i = some a) :
    stT P tf ins cntT k0 hk i = a := by
  unfold stT
  apply sl_some
  unfold shW
  have hne : (encL (ns := ns) (nr := nr) (sTape i)).val ≠ ns + 2 + nr + 2 := by
    have := (sTape (ns := ns) (nr := nr) i).isLt; rw [encL_val]; omega
  rw [if_neg hne, streamOf_sTape, Option.bind_some, h]

theorem stT_none (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (k0 : ℕ)
    (hk : k0 + WT ns nr ≤ tf) (i : Fin (ns + 1)) (h : ins i = none) :
    (stT P tf ins cntT k0 hk i).val = 2 + NL P + (k0 + (sTape (ns := ns) (nr := nr) i).val) := by
  unfold stT
  rw [sl_none]
  · rw [rg_val, encL_val]
  · unfold shW
    have hne : (encL (ns := ns) (nr := nr) (sTape i)).val ≠ ns + 2 + nr + 2 := by
      have := (sTape (ns := ns) (nr := nr) i).isLt; rw [encL_val]; omega
    rw [if_neg hne, streamOf_sTape, Option.bind_some, h]

theorem shW_cases (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (j : Fin (WT ns nr))
    (y : Fin (NW P tf)) (h : shW P tf ins cntT j = some y) :
    (j.val = ns + 2 + nr + 2 ∧ y = cntT) ∨ (∃ i, streamOf j = some i ∧ ins i = some y) := by
  unfold shW at h
  split_ifs at h with h1
  · exact Or.inl ⟨h1, (Option.some.inj h).symm⟩
  · right
    cases hs : streamOf j with
    | none => rw [hs] at h; simp at h
    | some i => rw [hs, Option.bind_some] at h; exact ⟨i, rfl, h⟩

theorem wfIn_stream (σ : WState ns nr) (W : ℕ) (s : Fin (ns + 1)) :
    wfIn σ W (encL (ns := ns) (nr := nr) (sTape s)) = σ.st s := by
  have hv : (encL (ns := ns) (nr := nr) (sTape s)).val = if s.val = 0 then 0 else s.val + 1 := rfl
  have hs := s.isLt
  rw [wfIn_val]
  by_cases h0 : s.val = 0
  · have e : s = 0 := Fin.ext h0
    subst e
    rw [if_neg (by rw [hv]; simp), if_pos (by rw [hv]; simp)]
  · rw [if_neg (by rw [hv, if_neg h0]; omega), if_neg (by rw [hv, if_neg h0]; omega),
      if_neg (by rw [hv, if_neg h0]; omega), dif_pos (by rw [hv, if_neg h0]; omega)]
    congr 1
    exact Fin.ext (by simp only; rw [hv, if_neg h0]; omega)

theorem wfIn_other (σ : WState ns nr) (W : ℕ) (j : Fin (WT ns nr)) (h1 : j.val ≠ ns + 2 + nr + 2)
    (h2 : streamOf j = none) : wfIn σ W j = [] := by
  unfold streamOf at h2
  rw [wfIn_val, if_neg h1]
  split_ifs at h2 with h3 h4
  have hj0 : j.val ≠ 0 := h3
  rw [if_neg hj0]
  by_cases hj1 : j.val = 1
  · rw [if_pos hj1]
  · rw [if_neg hj1, dif_neg (by omega)]

/-- **A word program docked on the worker's tapes.** -/
theorem wfD_step (Pm : WM ns nr) (W n : ℕ) (σ τ : WState ns nr) (hw : WExec (2 * W + 2) Pm σ τ n)
    (hs0 : ∀ i, σ.sh i = 0) (hv0 : ∀ r, σ.val r = 0) (hc0 : σ.cell = false)
    (ins : Fin (ns + 1) → Option (Fin (NW P tf))) (cntT : Fin (NW P tf)) (k0 : ℕ) (hk : k0 + WT ns nr ≤ tf)
    (hinsI : ∀ i j a, ins i = some a → ins j = some a → i = j)
    (hinsL : ∀ i a, ins i = some a → 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0)
    (hcL : 2 + NL P ≤ cntT.val ∧ cntT.val < 2 + NL P + k0) (hcs : ∀ i, ins i ≠ some cntT)
    (H0 : Fin (NW P tf) → ℕ) (A0 : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H0 A0 k0)
    (hin : ∀ i a, ins i = some a → A0 a = σ.st i ∧ H0 a = 0) (hnone : ∀ i, ins i = none → σ.st i = [])
    (hcnt : A0 cntT = List.replicate W true ∧ H0 cntT = 0) :
    ∃ A1 : Fin (NW P tf) → List Bool,
      Step (wfD P tf Pm ins cntT k0 hk) ((11 * W + 20) + 1 + (1 + 1 + (2 * n + 2))) H0 A0 H0 A1 ∧
      (∀ i, A1 (stT P tf ins cntT k0 hk i) = τ.st i) ∧ A1 cntT = List.replicate W true ∧
      (∀ y, (∀ j, sl P tf (shW P tf ins cntT) k0 hk j ≠ y) → A1 y = A0 y) ∧
      PristineH P tf H0 A1 (k0 + WT ns nr) := by
  obtain ⟨out, k, hs, hout, -, -, hcntO, -⟩ := wfM_step Pm W n σ τ hw hs0 hv0 hc0
  set sl0 := sl P tf (shW (nr := nr) P tf ins cntT) k0 hk with hsl0
  have hlow : ∀ j y, shW (nr := nr) P tf ins cntT j = some y → y.val < 2 + NL P + k0 := fun j y h => by
    rcases shW_cases P tf ins cntT j y h with ⟨-, rfl⟩ | ⟨i, -, hi⟩
    · exact hcL.2
    · exact (hinsL i y hi).2
  have hshL : ∀ j y, shW (nr := nr) P tf ins cntT j = some y → 2 + NL P ≤ y.val ∨ y.val < 2 := fun j y h => by
    rcases shW_cases P tf ins cntT j y h with ⟨-, rfl⟩ | ⟨i, -, hi⟩
    · exact Or.inl hcL.1
    · exact Or.inl (hinsL i y hi).1
  have hshI : ∀ i j y, shW (nr := nr) P tf ins cntT i = some y → shW (nr := nr) P tf ins cntT j = some y → i = j := by
    intro i j y hi hj
    rcases shW_cases P tf ins cntT i y hi with ⟨hi1, ei⟩ | ⟨s1, hs1, e1⟩ <;>
      rcases shW_cases P tf ins cntT j y hj with ⟨hj1, ej⟩ | ⟨s2, hs2, e2⟩
    · exact Fin.ext (by omega)
    · rw [ei] at e2; exact absurd e2 (hcs s2)
    · rw [ej] at e1; exact absurd e1 (hcs s1)
    · have e := hinsI s1 s2 y e1 e2
      subst e
      rw [streamOf_some j s1 hs2, streamOf_some i s1 hs1]
  have hinj : Function.Injective sl0 := sl_inj P tf _ k0 hk hshI hlow
  have hcntS : shW (nr := nr) P tf ins cntT (cntL (ns := ns) (nr := nr)) = some cntT := by
    unfold shW; rw [if_pos cntL_val]
  have hA : ∀ j, A0 (sl0 j) = wfIn σ W j := by
    intro j
    cases hsh : shW (nr := nr) P tf ins cntT j with
    | some y =>
      rw [hsl0, sl_some P tf _ k0 hk j y hsh]
      rcases shW_cases P tf ins cntT j y hsh with ⟨h1, rfl⟩ | ⟨s, hs1, e1⟩
      · rw [hcnt.1, wfIn_val, if_pos h1]
      · rw [(hin s y e1).1, streamOf_some j s hs1, wfIn_stream]
    | none =>
      rw [hsl0, sl_none P tf _ k0 hk j hsh, (hPr.1 _ (by rw [rg_val]; omega)).1]
      unfold shW at hsh
      split_ifs at hsh with h1
      cases hso : streamOf j with
      | none => rw [wfIn_other σ W j h1 hso]
      | some s =>
        rw [hso, Option.bind_some] at hsh
        rw [streamOf_some j s hso, wfIn_stream, hnone s hsh]
  have hH : ∀ j, H0 (sl0 j) = 0 := by
    intro j
    cases hsh : shW (nr := nr) P tf ins cntT j with
    | some y =>
      rw [hsl0, sl_some P tf _ k0 hk j y hsh]
      rcases shW_cases P tf ins cntT j y hsh with ⟨h1, rfl⟩ | ⟨s, hs1, e1⟩
      · exact hcnt.2
      · exact (hin s y e1).2
    | none =>
      rw [hsl0, sl_none P tf _ k0 hk j hsh]
      exact (hPr.1 _ (by rw [rg_val]; omega)).2
  have d1 := dockAny hs sl0 hinj H0 A0 hH hA
  rw [ExtDecompositionBatch.dockH_existing sl0 H0 (fun _ => 0) hH] at d1
  have hpr := pristineH_after P tf (shW (nr := nr) P tf ins cntT) k0 hk hlow hshL H0 A0 (fun _ => 0) out hPr
  rw [ExtDecompositionBatch.dockH_existing sl0 H0 (fun _ => 0) hH] at hpr
  refine ⟨install sl0 A0 out, d1, fun i => ?_, ?_, fun y hy => install_other _ _ _ _ hy, hpr⟩
  · show install sl0 A0 out (sl0 (encL (sTape i))) = τ.st i
    rw [install_slot _ hinj, hout, wenc_A_s]
  · rw [← sl_some P tf _ k0 hk _ cntT hcntS, install_slot _ hinj]
    exact hcntO

end Dock

/-! ## Any machine docked on the worker's tapes -/

section DockS
variable {kclk : ℕ} {E : Envelope} {B : TimeBudget kclk E} {I : PrimitiveInputs B} (P : FusedPrimitive I) (tf : ℕ)

/-- **A machine stage docked**: its shared tapes (`ins`) hold its inputs, its other tapes are a fresh region; the
worker's tapes end with the stage's outputs at its slots, everything else unchanged. -/
theorem dockS_step {t s : ℕ} (p : Machine t s) (n : ℕ) (tin tout : Fin t → List Bool) (hout : Fin t → ℕ)
    (h : Step p n (fun _ => 0) tin hout tout) (ins : Fin t → Option (Fin (NW P tf))) (k0 : ℕ) (hk : k0 + t ≤ tf)
    (hinsI : ∀ i j a, ins i = some a → ins j = some a → i = j)
    (hinsL : ∀ i a, ins i = some a → 2 + NL P ≤ a.val ∧ a.val < 2 + NL P + k0)
    (H0 : Fin (NW P tf) → ℕ) (A0 : Fin (NW P tf) → List Bool) (hPr : PristineH P tf H0 A0 k0)
    (hin : ∀ i a, ins i = some a → A0 a = tin i ∧ H0 a = 0) (hnone : ∀ i, ins i = none → tin i = []) :
    Step (RecoveryFocus.machine (sl P tf ins k0 hk) p) n H0 A0 (dockH (sl P tf ins k0 hk) H0 hout)
        (install (sl P tf ins k0 hk) A0 tout) ∧
      Function.Injective (sl P tf ins k0 hk) ∧
      PristineH P tf (dockH (sl P tf ins k0 hk) H0 hout) (install (sl P tf ins k0 hk) A0 tout) (k0 + t) := by
  have hlow : ∀ j y, ins j = some y → y.val < 2 + NL P + k0 := fun j y h => (hinsL j y h).2
  have hshL : ∀ j y, ins j = some y → 2 + NL P ≤ y.val ∨ y.val < 2 := fun j y h => Or.inl (hinsL j y h).1
  have hinj := sl_inj P tf ins k0 hk hinsI hlow
  have hA : ∀ j, A0 (sl P tf ins k0 hk j) = tin j := by
    intro j
    cases hj : ins j with
    | some a => rw [sl_some P tf ins k0 hk j a hj]; exact (hin j a hj).1
    | none => rw [sl_none P tf ins k0 hk j hj, (hPr.1 _ (by rw [rg_val]; omega)).1, hnone j hj]
  have hH : ∀ j, H0 (sl P tf ins k0 hk j) = 0 := by
    intro j
    cases hj : ins j with
    | some a => rw [sl_some P tf ins k0 hk j a hj]; exact (hin j a hj).2
    | none => rw [sl_none P tf ins k0 hk j hj]; exact (hPr.1 _ (by rw [rg_val]; omega)).2
  exact ⟨dockAny h _ hinj H0 A0 hH hA, hinj, pristineH_after P tf ins k0 hk hlow hshL H0 A0 hout tout hPr⟩

end DockS

end NearCubicWires.WireExponent3_5.UnionMachine.FrontWfDock
