import Proof.Wire_3_5.UnionMachine.FrontSlots
import Proof.Wire_3_5.UnionMachine.WalkKit

/-! # C6 front, the chain's kit: a register program with its own registers' fill

Every register program of the front runs on a layout whose register tapes start as `regTape cap 0` and whose cell
starts as `[false]`. **`wfM P`** does that itself from a count `1^W` (`cap = 2W + 2`): FrontFill's fill writes
`false^{2W+3}` on every register tape (and its marker), one action writes the cell, then the program runs compiled
and rewound (`WalkKit.wm_stepJ`). Local layout: the program's `ns + 2 + nr` tapes (`wenc`), its log, the fill's marker,
the count.
* `wfIn σ W` (the entry: the program's streams, blank registers, cell, log and marker, `1^W`);
* **`wfM_step`**: from `wfIn σ W` to the encoded exit state `τ`, the log `0^k`, the marker `0^{2W+3}`, `1^W` kept.

Paper quantity: none (the front's plumbing). -/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
open NearCubicWires NearCubicWires.LocalBitMultitape NearCubicWires.RepairOrdinary NearCubicWires.ExtDecompositionBatch
open NearCubicWires.RepairOrdinary.RecoveryRootRound (install install_slot install_other)
open NearCubicWires.WireExponent3_5.FinalPass.Tm
open NearCubicWires.WireExponent3_5.UnionMachine.FrontSlots
open NearCubicWires.WireExponent3_5.UnionMachine.FrontLoopKit

section WM
variable {ns nr : ℕ}

/-- The local layout's size. -/
abbrev WT (ns nr : ℕ) : ℕ := ns + 2 + nr + 3

/-- The program's tapes, its log, the fill's marker, the count. -/
def encL (i : Fin (ns + 2 + nr)) : Fin (WT ns nr) := ⟨i.val, by have := i.isLt; unfold WT; omega⟩
def logL : Fin (WT ns nr) := ⟨ns + 2 + nr, by unfold WT; omega⟩
def mkL : Fin (WT ns nr) := ⟨ns + 2 + nr + 1, by unfold WT; omega⟩
def cntL : Fin (WT ns nr) := ⟨ns + 2 + nr + 2, by unfold WT; omega⟩

/-- The register tapes. -/
def tgtL (i : Fin (WT ns nr)) : Bool := decide (ns + 2 ≤ i.val ∧ i.val < ns + 2 + nr)

/-- The rewound program's slots: the program's tapes and its log. -/
def rwSl (j : Fin (ns + 2 + nr + 1)) : Fin (WT ns nr) := ⟨j.val, by have := j.isLt; unfold WT; omega⟩

theorem rwSl_inj : Function.Injective (rwSl (ns := ns) (nr := nr)) := fun a b h =>
  Fin.ext (by simpa [rwSl] using congrArg Fin.val h)

/-- **The program with its registers' fill.** -/
noncomputable def wfM (P : WM ns nr) :=
  Composition.machine (FrontFill.fillP (cntL (ns := ns) (nr := nr)) mkL tgtL).compile
    (Composition.machine (FrontKit.cellP (encL (ns := ns) (nr := nr) ⟨1, by omega⟩)).compile
      (RecoveryFocus.machine rwSl (Rewind.machine P.toProg.compile)))

/-- The entry: the program's streams, every other tape blank, `1^W` on the count. -/
def wfIn (σ : WState ns nr) (W : ℕ) : Fin (WT ns nr) → List Bool := fun i =>
  if i.val = ns + 2 + nr + 2 then List.replicate W true
  else if i.val = 0 then σ.st 0
  else if i.val = 1 then []
  else if h : i.val ≤ ns + 1 then σ.st ⟨i.val - 1, by omega⟩
  else []

theorem wenc_A_v (cap : ℕ) (σ : WState ns nr) (j : Fin (ns + 2 + nr)) :
    (wenc cap σ).A j = if j.val = 0 then σ.st 0 else if j.val = 1 then [σ.cell]
      else if h : j.val ≤ ns + 1 then σ.st ⟨j.val - 1, by omega⟩
      else regTape cap (σ.val ⟨j.val - (ns + 2), by omega⟩) := by
  simp only [wenc, role]
  split_ifs <;> rfl

theorem regTape_zero' (cap : ℕ) : regTape cap 0 = List.replicate (cap + 1) false := by
  simp [regTape, List.replicate_succ]

theorem mkL_val : (mkL (ns := ns) (nr := nr)).val = ns + 2 + nr + 1 := rfl
theorem cntL_val : (cntL (ns := ns) (nr := nr)).val = ns + 2 + nr + 2 := rfl
theorem encL_val (i : Fin (ns + 2 + nr)) : (encL (ns := ns) (nr := nr) i).val = i.val := rfl
theorem rwSl_val (j : Fin (ns + 2 + nr + 1)) : (rwSl (ns := ns) (nr := nr) j).val = j.val := rfl

theorem side_iff (i : Fin (WT ns nr)) :
    FrontFill.side mkL tgtL i ↔ (ns + 2 ≤ i.val ∧ i.val < ns + 2 + nr) ∨ i.val = ns + 2 + nr + 1 := by
  unfold FrontFill.side tgtL
  constructor
  · rintro (h | h)
    · left; simpa using h
    · right; rw [h, mkL_val]
  · rintro (h | h)
    · left; simpa using h
    · right; exact Fin.ext (by rw [h, mkL_val])

theorem wfIn_val (σ : WState ns nr) (W : ℕ) (i : Fin (WT ns nr)) :
    wfIn σ W i = if i.val = ns + 2 + nr + 2 then List.replicate W true
      else if i.val = 0 then σ.st 0 else if i.val = 1 then []
      else if h : i.val ≤ ns + 1 then σ.st ⟨i.val - 1, by omega⟩ else [] := rfl

/-- **The program with its registers' fill, as a Step.** -/
theorem wfM_step (P : WM ns nr) (W n : ℕ) (σ τ : WState ns nr) (hw : WExec (2 * W + 2) P σ τ n)
    (hs0 : ∀ i, σ.sh i = 0) (hv0 : ∀ r, σ.val r = 0) (hc0 : σ.cell = false) :
    ∃ (out : Fin (WT ns nr) → List Bool) (k : ℕ),
      Step (wfM P) ((11 * W + 20) + 1 + (1 + 1 + (2 * n + 2))) (fun _ => 0) (wfIn σ W) (fun _ => 0) out ∧
      (∀ i, out (encL i) = (wenc (2 * W + 2) τ).A i) ∧ out logL = List.replicate k false ∧
      out mkL = List.replicate (2 * W + 3) false ∧ out cntL = List.replicate W true ∧ k ≤ n := by
  have hca : (cntL (ns := ns) (nr := nr)) ≠ mkL := fun e => by
    have := congrArg Fin.val e; rw [cntL_val, mkL_val] at this; omega
  have hct : tgtL (cntL (ns := ns) (nr := nr)) = false := by simp [tgtL, cntL_val]
  have hat : tgtL (mkL (ns := ns) (nr := nr)) = false := by simp [tgtL, mkL_val]
  -- the fill
  have g1 := FrontKit.fill_ready cntL mkL tgtL (wfIn σ W) W hca hct hat
    (by rw [wfIn_val, if_pos cntL_val])
    (fun i hi => by
      rw [side_iff] at hi
      rw [wfIn_val, if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)])
  set A1 : Fin (WT ns nr) → List Bool := fun i =>
      if FrontFill.side mkL tgtL i then List.replicate (2 * W + 3) false else wfIn σ W i with hA1
  have A1s : ∀ i, FrontFill.side mkL tgtL i → A1 i = List.replicate (2 * W + 3) false := fun i hi => by
    simp only [hA1, if_pos hi]
  have A1n : ∀ i, ¬ FrontFill.side mkL tgtL i → A1 i = wfIn σ W i := fun i hi => by
    simp only [hA1, if_neg hi]
  -- the cell
  set c1 : Fin (WT ns nr) := encL (ns := ns) (nr := nr) ⟨1, by omega⟩ with hc1
  have c1v : c1.val = 1 := rfl
  have hcell : A1 c1 = [] := by
    rw [A1n c1 (by rw [side_iff, c1v]; omega), wfIn_val]
    simp only [c1v]
    rw [if_neg (by omega), if_neg (by omega)]
    simp
  have g2 := FrontKit.cell_ready c1 A1 hcell
  set A2 := Function.update A1 c1 [false] with hA2
  -- the program, rewound
  obtain ⟨out, k, hs, hout, hlog, hk⟩ := WalkKit.wm_stepJ (2 * W + 2) P σ τ n hw (FrontKit.wenc_H_zero _ σ hs0 hv0)
  have hin : ∀ j, A2 (rwSl j) = Fin.addCases (wenc (2 * W + 2) σ).A (fun _ : Fin 1 => ([] : List Bool)) j := by
    intro j
    refine Fin.addCases (m := ns + 2 + nr) (n := 1) (fun i => ?_) (fun o => ?_) j
    · rw [Fin.addCases_left, wenc_A_v]
      have hi := i.isLt
      have rv : (rwSl (ns := ns) (nr := nr) (Fin.castAdd 1 i)).val = i.val := rfl
      by_cases h1 : i.val = 1
      · have e : rwSl (Fin.castAdd 1 i) = c1 := Fin.ext (by rw [rv, c1v, h1])
        rw [e, hA2, Function.update_self, if_neg (by omega), if_pos h1, hc0]
      · have hne : rwSl (Fin.castAdd 1 i) ≠ c1 := fun e => h1 (by rw [← rv, e, c1v])
        rw [hA2, Function.update_of_ne hne]
        by_cases hr : ns + 2 ≤ i.val
        · rw [A1s _ (by rw [side_iff, rv]; omega), if_neg (by omega), if_neg h1, dif_neg (by omega), hv0,
            regTape_zero']
        · rw [A1n _ (by rw [side_iff, rv]; omega), wfIn_val]
          simp only [rv]
          rw [if_neg (by omega)]
          by_cases h0 : i.val = 0
          · rw [if_pos h0, if_pos h0]
          · rw [if_neg h0, if_neg h1, if_neg h0, if_neg h1, dif_pos (by omega), dif_pos (by omega)]
    · rw [Fin.addCases_right]
      have rv : (rwSl (ns := ns) (nr := nr) (Fin.natAdd (ns + 2 + nr) o)).val = ns + 2 + nr := by
        simp [rwSl, Subsingleton.elim o 0]
      have hne : rwSl (Fin.natAdd (ns + 2 + nr) o) ≠ c1 := fun e => by
        have := congrArg Fin.val e; rw [rv, c1v] at this; omega
      rw [hA2, Function.update_of_ne hne, A1n _ (by rw [side_iff, rv]; omega), wfIn_val]
      simp only [rv]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), dif_neg (by omega)]
  have g3 := dockZ hs rwSl rwSl_inj A2 hin
  refine ⟨_, k, Step.seq (step_of_ready g1) (Step.seq (step_of_ready g2) g3), fun i => ?_, ?_, ?_, ?_, hk⟩
  · have e : encL (ns := ns) (nr := nr) i = rwSl (Fin.castAdd 1 i) := Fin.ext rfl
    rw [e, install_slot _ rwSl_inj, hout]
  · have e : (logL (ns := ns) (nr := nr)) = rwSl (Fin.natAdd (ns + 2 + nr) 0) := Fin.ext (by simp [logL, rwSl])
    rw [e, install_slot _ rwSl_inj, hlog]
  · have hn : ∀ j, rwSl j ≠ (mkL (ns := ns) (nr := nr)) := fun j e => by
      have h1 := congrArg Fin.val e; have := j.isLt; rw [rwSl_val, mkL_val] at h1; omega
    have hne : (mkL (ns := ns) (nr := nr)) ≠ c1 := fun e => by
      have := congrArg Fin.val e; rw [mkL_val, c1v] at this; omega
    rw [install_other _ _ _ _ hn, hA2, Function.update_of_ne hne, A1s _ (by rw [side_iff, mkL_val]; omega)]
  · have hn : ∀ j, rwSl j ≠ (cntL (ns := ns) (nr := nr)) := fun j e => by
      have h1 := congrArg Fin.val e; have := j.isLt; rw [rwSl_val, cntL_val] at h1; omega
    have hne : (cntL (ns := ns) (nr := nr)) ≠ c1 := fun e => by
      have := congrArg Fin.val e; rw [cntL_val, c1v] at this; omega
    rw [install_other _ _ _ _ hn, hA2, Function.update_of_ne hne, A1n _ (by rw [side_iff, cntL_val]; omega),
      wfIn_val, if_pos cntL_val]

end WM

end NearCubicWires.WireExponent3_5.UnionMachine.FrontWM
